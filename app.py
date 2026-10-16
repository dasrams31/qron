#!/usr/bin/env python3
"""Qron - QR code generator for onion URLs.

Pure Python stdlib: QR encoder (byte mode, EC level M) + PNG encoder.
No external dependencies.
"""

import html
import re
import struct
import urllib.parse
import zlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

PORT = 18099
URL_MAX = 200

ONION_RE = re.compile(r"^https?://[a-z2-7]{16,62}\.onion(:\d+)?(/.*)?$", re.I)


# ---------------------------------------------------------- Galois field ---

_EXP = [0] * 512
_LOG = [0] * 256


def _init_gf():
    x = 1
    for i in range(255):
        _EXP[i] = x
        _LOG[x] = i
        x <<= 1
        if x & 0x100:
            x ^= 0x11D
    for i in range(255, 512):
        _EXP[i] = _EXP[i - 255]


_init_gf()


def gf_mul(a, b):
    return 0 if a == 0 or b == 0 else _EXP[_LOG[a] + _LOG[b]]


def rs_generator(nsym):
    """Reed-Solomon generator polynomial coefficients."""
    g = [1]
    for i in range(nsym):
        g = [gf_mul(c, _EXP[i]) for c in g] + [0]
        for j in range(len(g) - 1):
            g[j] ^= g[j + 1] if j + 1 < len(g) else 0
        # polynomial multiply by (x + a^i): shift and add
    # redo cleanly:
    g = [1]
    for i in range(nsym):
        nxt = [0] * (len(g) + 1)
        for j, c in enumerate(g):
            nxt[j] ^= gf_mul(c, _EXP[i])
            nxt[j + 1] ^= c
        g = nxt
    return g


def rs_encode(data, nsym):
    gen = rs_generator(nsym)
    res = list(data) + [0] * nsym
    for i in range(len(data)):
        coef = res[i]
        if coef:
            for j in range(len(gen)):
                res[i + j] ^= gf_mul(gen[j], coef)
    return res[len(data):]


# ---------------------------------------------------------------- QR code ---

# version: (size, total_codewords, ec_per_block, [(block_count, data_codewords)])
_VERSIONS_M = {
    1: (21, 26, 10, [(1, 16)]),
    2: (25, 44, 16, [(1, 28)]),
    3: (29, 70, 26, [(1, 44)]),
    4: (33, 100, 18, [(2, 32)]),
    5: (37, 134, 24, [(2, 43)]),
    6: (41, 172, 16, [(4, 27)]),
    7: (45, 196, 18, [(4, 31)]),
}

# byte-mode char capacity at EC level M
_CAP_M = {1: 14, 2: 26, 3: 42, 4: 62, 5: 84, 6: 106, 7: 122}

_ALIGN_POS = {
    2: [6, 18], 3: [6, 22], 4: [6, 26], 5: [6, 30],
    6: [6, 34], 7: [6, 22, 38],
}

# format info BCH (ec level M = 00)
_FORMAT_M = [
    0x5412, 0x5125, 0x5E7C, 0x5B4B, 0x45F9, 0x40CE, 0x4F97, 0x4AA0,
    0x77C4, 0x72F3, 0x7DAA, 0x789D, 0x662F, 0x6318, 0x6C41, 0x6976,
    0x1689, 0x13BE, 0x1CE7, 0x19D0, 0x0762, 0x0255, 0x0D0C, 0x083B,
    0x355F, 0x3068, 0x3F31, 0x3A06, 0x24B4, 0x2183, 0x2EDA, 0x2BED,
]


def _bits(data, n):
    return [(data >> (n - 1 - i)) & 1 for i in range(n)]


class QRCode:
    def __init__(self, text):
        raw = text.encode("utf-8")
        self.version = next(v for v in range(1, 8) if len(raw) <= _CAP_M[v])
        size, total, ec, groups = _VERSIONS_M[self.version]
        self.size = size
        self.matrix = [[None] * size for _ in range(size)]
        self._function = [[False] * size for _ in range(size)]

        # --- encode data bits (byte mode) ---
        bits = []
        bits += [0, 1, 0, 0]  # byte mode
        bits += _bits(len(raw), 8)  # char count (versions 1-9)
        for b in raw:
            bits += _bits(b, 8)
        data_cw = total - ec * sum(g[0] for g in groups)
        max_bits = data_cw * 8
        # terminator
        bits += [0] * min(4, max_bits - len(bits))
        while len(bits) % 8:
            bits.append(0)
        data = []
        for i in range(0, len(bits), 8):
            v = 0
            for b in bits[i:i + 8]:
                v = (v << 1) | b
            data.append(v)
        # pad bytes
        pad = [0xEC, 0x11]
        pi = 0
        while len(data) < data_cw:
            data.append(pad[pi % 2])
            pi += 1

        # --- split into blocks, RS encode, interleave ---
        blocks = []
        idx = 0
        for count, dcw in groups:
            for _ in range(count):
                blk = data[idx:idx + dcw]
                idx += dcw
                blocks.append((blk, rs_encode(blk, ec)))
        inter = []
        max_dcw = max(len(b[0]) for b in blocks)
        for i in range(max_dcw):
            for blk, _ in blocks:
                if i < len(blk):
                    inter.append(blk[i])
        for i in range(ec):
            for _, ecb in blocks:
                inter.append(ecb[i])
        self.data_bits = []
        for cw in inter:
            self.data_bits += _bits(cw, 8)

        # --- function patterns ---
        self._finder(0, 0)
        self._finder(size - 7, 0)
        self._finder(0, size - 7)
        self._timing()
        self._alignment()
        self._dark_module()
        self._reserve_format()

        # --- place data, try masks, pick best ---
        best = None
        best_pen = None
        for mask in range(8):
            m = [row[:] for row in self.matrix]
            self._place_data(m, mask)
            pen = self._penalty(m)
            if best_pen is None or pen < best_pen:
                best_pen = pen
                best = (m, mask)
        self.matrix, self.mask = best
        self._draw_format(self.mask)

    # -- patterns --
    def _set(self, x, y, v, func=True):
        if 0 <= x < self.size and 0 <= y < self.size:
            self.matrix[y][x] = v
            if func:
                self._function[y][x] = True

    def _finder(self, x, y):
        pat = [0b1111111, 0b1000001, 0b1011101, 0b1011101,
               0b1011101, 0b1000001, 0b1111111]
        for dy in range(-1, 8):
            for dx in range(-1, 8):
                v = 0
                if 0 <= dx < 7 and 0 <= dy < 7:
                    v = (pat[dy] >> (6 - dx)) & 1
                self._set(x + dx, y + dy, v)

    def _timing(self):
        for i in range(8, self.size - 8):
            v = 1 if i % 2 == 0 else 0
            if not self._function[6][i]:
                self._set(i, 6, v)
            if not self._function[i][6]:
                self._set(6, i, v)

    def _alignment(self):
        pos = _ALIGN_POS.get(self.version, [])
        for y in pos:
            for x in pos:
                if self._function[y][x]:
                    continue
                for dy in range(-2, 3):
                    for dx in range(-2, 3):
                        v = 1 if max(abs(dx), abs(dy)) != 1 else 0
                        self._set(x + dx, y + dy, v)

    def _dark_module(self):
        self._set(4 * self.version + 9, 8, 1)

    def _reserve_format(self):
        s = self.size

        def reserve(x, y):
            self._function[y][x] = True
            if self.matrix[y][x] is None:
                self.matrix[y][x] = 0
        for i in range(15):
            # top-left copies
            if i < 6:
                reserve(i, 8)
                reserve(8, i)
            elif i < 8:
                reserve(i + 1, 8)
                reserve(8, i + 1)
            else:
                reserve(s - 15 + i, 8)
                reserve(8, s - 15 + i)

    def _draw_format(self, mask):
        f = _FORMAT_M[mask]
        bits = _bits(f, 15)
        s = self.size

        def put(x, y, v):
            self.matrix[y][x] = v
            self._function[y][x] = True
        # around top-left finder
        for i in range(6):
            put(8, i, bits[i])
            put(i, 8, bits[i])
        put(8, 7, bits[6])
        put(8, 8, bits[7])
        put(7, 8, bits[8])
        for i in range(6):
            put(5 - i, 8, bits[9 + i])
        # top-right / bottom-left
        for i in range(s - 7, s):
            put(i, 8, bits[s - 1 - i])
            put(8, i, bits[s - 1 - i])

    # -- data placement --
    @staticmethod
    def _mask_bit(mask, x, y):
        if mask == 0:
            return (x + y) % 2 == 0
        if mask == 1:
            return y % 2 == 0
        if mask == 2:
            return x % 3 == 0
        if mask == 3:
            return (x + y) % 3 == 0
        if mask == 4:
            return (x // 3 + y // 2) % 2 == 0
        if mask == 5:
            return (x * y) % 2 + (x * y) % 3 == 0
        if mask == 6:
            return ((x * y) % 2 + (x * y) % 3) % 2 == 0
        return ((x + y) % 2 + (x * y) % 3) % 2 == 0

    def _place_data(self, m, mask):
        bits = self.data_bits
        bi = 0
        s = self.size
        x = s - 1
        upward = True
        while x > 0:
            if x == 6:
                x -= 1
            for _ in range(s):
                y = s - 1 - _ if upward else _
                for dx in (0, -1):
                    xx = x + dx
                    if self._function[y][xx]:
                        continue
                    v = bits[bi] if bi < len(bits) else 0
                    bi += 1
                    if self._mask_bit(mask, xx, y):
                        v ^= 1
                    m[y][xx] = v
            x -= 2
            upward = not upward

    # -- penalty (mask selection) --
    def _penalty(self, m):
        s = self.size
        pen = 0
        # rule 1: consecutive same in rows/cols
        for y in range(s):
            run = 1
            for x in range(1, s):
                if m[y][x] == m[y][x - 1]:
                    run += 1
                else:
                    if run >= 5:
                        pen += 3 + (run - 5)
                    run = 1
            if run >= 5:
                pen += 3 + (run - 5)
        for x in range(s):
            run = 1
            for y in range(1, s):
                if m[y][x] == m[y - 1][x]:
                    run += 1
                else:
                    if run >= 5:
                        pen += 3 + (run - 5)
                    run = 1
            if run >= 5:
                pen += 3 + (run - 5)
        # rule 2: 2x2 blocks
        for y in range(s - 1):
            for x in range(s - 1):
                v = m[y][x]
                if m[y][x + 1] == v and m[y + 1][x] == v and m[y + 1][x + 1] == v:
                    pen += 3
        # rule 3: finder-like patterns
        pat1 = [1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0]
        pat2 = [0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1]
        for y in range(s):
            for x in range(s - 10):
                seg = [m[y][x + i] for i in range(11)]
                if seg == pat1 or seg == pat2:
                    pen += 40
        for x in range(s):
            for y in range(s - 10):
                seg = [m[y + i][x] for i in range(11)]
                if seg == pat1 or seg == pat2:
                    pen += 40
        # rule 4: dark ratio
        dark = sum(sum(row) for row in m)
        ratio = abs(dark * 100 / (s * s) - 50) // 5
        pen += int(ratio * 10)
        return pen


# ---------------------------------------------------------------- PNG ---

def png_encode(matrix, scale=8, border=4):
    """matrix of 0/1 -> PNG bytes (8-bit grayscale)."""
    s = len(matrix)
    px = (s + border * 2) * scale
    rows = []
    for y in range(px):
        row = bytearray([0])  # filter type 0
        my = y // scale - border
        for x in range(px):
            mx = x // scale - border
            v = 255
            if 0 <= mx < s and 0 <= my < s and matrix[my][mx]:
                v = 0
            row.append(v)
        rows.append(bytes(row))
    raw = b"".join(rows)
    comp = zlib.compress(raw, 9)

    def chunk(typ, data):
        c = struct.pack(">I", len(data)) + typ + data
        c += struct.pack(">I", zlib.crc32(typ + data) & 0xFFFFFFFF)
        return c

    ihdr = struct.pack(">IIBBBBB", px, px, 8, 0, 0, 0, 0)
    return (b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", ihdr)
            + chunk(b"IDAT", comp) + chunk(b"IEND", b""))


def qr_png(text, scale=8):
    return png_encode(QRCode(text).matrix, scale=scale)


# ---------------------------------------------------------------- web ---

def esc(s):
    return html.escape(s or "", quote=True)


CSS = """
*{box-sizing:border-box;margin:0;padding:0}
:root{--bg:#0d0d0e;--panel:#151517;--panel2:#1c1c1f;--border:#232326;--border2:#323237;
--text:#f4f4f5;--muted:#9c9ca6;--faint:#63636c;--acc:#8ab4ff}
html{-webkit-text-size-adjust:100%%}
body{background:var(--bg);color:var(--text);font-family:-apple-system,BlinkMacSystemFont,
"Segoe UI",Roboto,Helvetica,Arial,sans-serif;line-height:1.55;font-size:15px;
-webkit-font-smoothing:antialiased}
a{color:inherit;text-decoration:none}
.wrap{max-width:640px;margin:0 auto;padding:0 20px;min-height:100vh;display:flex;
flex-direction:column}
.topbar{padding:18px 0;display:flex;align-items:center;justify-content:space-between}
.wordmark{font-size:20px;font-weight:800;letter-spacing:-.03em}
.wordmark .dot{color:var(--faint)}
.tag{font-size:12px;color:var(--faint)}
.main{flex:1;display:flex;flex-direction:column;justify-content:center;padding:20px 0 40px}
.hero{text-align:center;margin-bottom:26px}
.hero h1{font-size:28px;font-weight:800;letter-spacing:-.03em;margin-bottom:8px}
.hero p{color:var(--muted);font-size:14.5px}
form.gen{display:flex;flex-direction:column;gap:12px}
input[type=text]{width:100%%;background:var(--panel);border:1px solid var(--border2);
border-radius:14px;padding:15px 18px;color:var(--text);font-size:15px;
font-family:ui-monospace,Menlo,Consolas,monospace;min-height:56px}
input[type=text]:focus{outline:none;border-color:var(--muted)}
button.btn{background:var(--text);color:#0d0d0e;border:none;border-radius:14px;
padding:15px 28px;font-weight:700;font-size:16px;cursor:pointer;min-height:56px;
font-family:inherit;width:100%%}
button.btn:active{transform:scale(.98)}
.result{text-align:center}
.qrbox{background:#fff;border-radius:18px;padding:22px;display:inline-block;margin-bottom:18px}
.qrbox img{display:block;width:min(72vw,300px);height:auto;image-rendering:pixelated}
.url{font-family:ui-monospace,Menlo,Consolas,monospace;font-size:12.5px;color:var(--muted);
word-break:break-all;margin-bottom:16px;padding:0 8px}
.dlrow{display:flex;gap:10px;justify-content:center;flex-wrap:wrap}
a.dlbtn{background:var(--panel2);border:1px solid var(--border2);color:var(--text);
border-radius:12px;padding:13px 24px;font-size:14.5px;font-weight:700;min-height:50px;
display:inline-flex;align-items:center}
a.dlbtn:hover{border-color:var(--muted)}
a.again{color:var(--faint);font-size:13.5px;margin-top:18px;display:inline-block}
a.again:hover{color:var(--text)}
.err{background:rgba(244,63,94,.08);border:1px solid rgba(244,63,94,.35);color:#fda4b4;
padding:12px 16px;border-radius:12px;margin-bottom:16px;font-size:14px;text-align:center}
.hint{font-size:12.5px;color:var(--faint);margin-top:16px;text-align:center}
.footer{padding:24px 0 32px;text-align:center;color:var(--faint);font-size:12px}
@media(max-width:660px){
.wrap{padding:0 16px}
.hero h1{font-size:24px}
.topbar{padding:14px 0}
input[type=text]{font-size:16px}
}
"""

PAGE_TOP = ("<!DOCTYPE html><html lang='en'><head><meta charset='utf-8'>"
            "<meta name='viewport' content='width=device-width,initial-scale=1,viewport-fit=cover'>"
            "<meta name='description' content='QR code generator for onion addresses.'>"
            "<title>%s - Qron</title><style>" + CSS + "</style></head><body>"
            "<div class='wrap'><div class='topbar'>"
            "<a class='wordmark' href='/'>Qron<span class='dot'>.</span></a>"
            "<span class='tag'>QR for onion</span></div><div class='main'>")
PAGE_BOT = ("</div><div class='footer'>Qron &mdash; QR codes for .onion addresses<br>"
            "Generated locally. Nothing uploaded.</div></div></body></html>")


def home_page(err=""):
    ehtml = "<div class='err'>%s</div>" % esc(err) if err else ""
    body = ("<div class='hero'><h1>QR it.</h1>"
            "<p>Turn any .onion address into a scannable QR code.</p></div>"
            "%s<form class='gen' method='post' action='/'>"
            "<input type='text' name='url' maxlength='200' "
            "placeholder='http://....onion/...' autocapitalize='off' "
            "autocomplete='off' autocorrect='off' spellcheck='false' required>"
            "<button class='btn' type='submit'>Generate QR</button></form>"
            "<p class='hint'>QR codes are generated on this server. "
            "Only .onion URLs accepted.</p>") % ehtml
    return PAGE_TOP % "Generate" + body + PAGE_BOT


def result_page(url, png_b64):
    import base64
    b64 = base64.b64encode(png_b64).decode("ascii")
    body = ("<div class='result'>"
            "<div class='qrbox'><img alt='QR code' src='data:image/png;base64,%s'></div>"
            "<div class='url'>%s</div>"
            "<div class='dlrow'>"
            "<a class='dlbtn' download='qron.png' href='data:image/png;base64,%s'>"
            "Download PNG</a></div>"
            "<a class='again' href='/'>Generate another</a></div>") % (b64, esc(url), b64)
    return PAGE_TOP % "QR code" + body + PAGE_BOT


def normalize_url(raw):
    raw = (raw or "").strip()
    if not raw or len(raw) > URL_MAX:
        return None
    if "://" not in raw:
        raw = "http://" + raw
    if not ONION_RE.match(raw):
        return None
    return raw


class Handler(BaseHTTPRequestHandler):
    server_version = "Qron/1.0"
    protocol_version = "HTTP/1.1"

    def send_html(self, code, html_body):
        data = html_body.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def read_form(self):
        try:
            ln = int(self.headers.get("Content-Length", 0))
        except ValueError:
            return None
        if ln <= 0 or ln > 4096:
            return None
        raw = self.rfile.read(ln)
        try:
            return dict(urllib.parse.parse_qsl(raw.decode("utf-8", "replace")))
        except Exception:
            return None

    def do_GET(self):
        path = urllib.parse.urlparse(self.path).path
        if path == "/":
            self.send_html(200, home_page())
        else:
            self.send_html(404, PAGE_TOP % "Not found"
                           + "<div class='hero'><h1>Not found.</h1></div>" + PAGE_BOT)

    def do_POST(self):
        path = urllib.parse.urlparse(self.path).path
        if path != "/":
            self.send_html(404, PAGE_TOP % "Not found"
                           + "<div class='hero'><h1>Not found.</h1></div>" + PAGE_BOT)
            return
        form = self.read_form()
        if form is None:
            self.send_html(400, home_page("Bad request."))
            return
        url = normalize_url(form.get("url", ""))
        if not url:
            self.send_html(400, home_page("Only valid .onion URLs (max 200 chars)."))
            return
        try:
            png = qr_png(url, scale=8)
        except Exception:
            self.send_html(400, home_page("URL too long for a QR code."))
            return
        self.send_html(200, result_page(url, png))

    def log_message(self, *args):
        pass


def main():
    srv = ThreadingHTTPServer(("127.0.0.1", PORT), Handler)
    print("Qron on 127.0.0.1:%d" % PORT, flush=True)
    srv.serve_forever()


if __name__ == "__main__":
    main()
