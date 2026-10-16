# Qron

QR code generator for .onion addresses. Pure Python, zero dependencies.

- Paste an .onion URL, get a scannable QR code
- Download as PNG
- Only .onion URLs accepted

## Stack

Python stdlib only. Includes a from-scratch QR encoder
(byte mode, EC level M) and PNG encoder.

## Run

```
python3 app.py  # 127.0.0.1:18099
```

Deploy as a Tor hidden service.
