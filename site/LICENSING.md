Files in site/ and their origin:

- installer.html, installer.js, fm1ota.js, fm1pkg.js: the FM-1 web installer from ORBIT (github.com/dspaudio/orbit), GPL-3.0-only,
  copyright its authors; copy adapted to FORMALFRED. The OTA protocol library is unchanged.
- coi-serviceworker.min.js: github.com/gzuidhof/coi-serviceworker, MIT. It adds the cross-origin isolation headers
  GitHub Pages cannot send, which the simulator needs for SharedArrayBuffer.
- index.html: ours.
