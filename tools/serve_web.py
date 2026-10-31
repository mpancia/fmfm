#!/usr/bin/env python3
"""Serve build/web on localhost. The simulator needs a cross-origin-isolated page
(SharedArrayBuffer), which only works with these two headers."""
import functools, http.server, sys

class Handler(http.server.SimpleHTTPRequestHandler):
    def end_headers(self):
        self.send_header("Cross-Origin-Opener-Policy", "same-origin")
        self.send_header("Cross-Origin-Embedder-Policy", "require-corp")
        self.send_header("Cache-Control", "no-store")
        super().end_headers()

port = int(sys.argv[1]) if len(sys.argv) > 1 else 8000
root = sys.argv[2] if len(sys.argv) > 2 else "build/web"
h = functools.partial(Handler, directory=root)
with http.server.ThreadingHTTPServer(("127.0.0.1", port), h) as s:
    print(f"FM-1 simulator: http://localhost:{port}/   (Ctrl-C to stop)")
    try:
        s.serve_forever()
    except KeyboardInterrupt:
        pass
