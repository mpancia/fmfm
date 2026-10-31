/* Plays the ring the worker fills. Silence (and a counted underrun) if it runs dry. */
class FM1Out extends AudioWorkletProcessor {
  constructor(o) {
    super();
    const p = o.processorOptions;
    this.ctl = new Int32Array(p.ctl); this.ring = new Int16Array(p.ring); this.mask = p.ringFrames - 1;
    this.primed = false;
  }
  process(_in, outputs) {
    const L = outputs[0][0], R = outputs[0][1] || L, len = L.length;
    const w = Atomics.load(this.ctl, 13), r = Atomics.load(this.ctl, 14), have = (w - r) | 0;
    if (!this.primed) {                      // let the buffer fill before the first sample
      if (have >= 1024) this.primed = true; else return true;
    }
    if (have < len) { Atomics.add(this.ctl, 18, 1); this.primed = false; return true; }
    for (let i = 0; i < len; i++) {
      const j = ((r + i) & this.mask) * 2;
      L[i] = this.ring[j] / 32768; R[i] = this.ring[j + 1] / 32768;
    }
    Atomics.store(this.ctl, 14, (r + len) | 0);
    Atomics.notify(this.ctl, 14);
    return true;
  }
}
registerProcessor('fm1-out', FM1Out);
