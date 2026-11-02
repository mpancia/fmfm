// Arrow keys or space: the next card or line, then the next slide. N: the presenter's notes. P: the demo video on
// its slide, R rewinds it. S: a five-minute bar across the top of the screen. The hash keeps the place. ?all=1 lays
// every slide out on one page with its notes, which is also how it prints.
const slides = [...document.querySelectorAll(".slide")];
const count = document.querySelector(".count");
const progress = document.querySelector(".progress");
const bar = document.querySelector(".clock .bar");
const MINUTES = 5;
const all = new URLSearchParams(location.search).get("all") === "1";
let at = Math.min(slides.length - 1, Math.max(0, parseInt(location.hash.slice(1) || "0", 10) || 0));
let started = 0;
slides.forEach(() => progress.append(document.createElement("span")));

// The opening's animations run when its slide gets the class `play`: the first key on it (or R) starts them, so the
// screen stays dark until the presenter is ready; taking the class off and putting it back replays them.
function replay(slide) {
  slide.classList.remove("play");
  void slide.offsetWidth;
  slide.classList.add("play");
}

function show(i, fragsOn) {
  const leaving = slides[at].querySelector("video");
  if (leaving) leaving.pause();
  at = i;
  slides.forEach((s, k) => {
    s.classList.toggle("on", k === i);
    const notes = s.querySelector("aside.notes");
    if (notes) notes.classList.toggle("on", k === i);
  });
  slides[i].querySelectorAll(".frag").forEach(f => f.classList.toggle("on", fragsOn));
  [...progress.children].forEach((tick, k) => tick.classList.toggle("on", k === i));
  document.body.classList.toggle("dark", slides[i].classList.contains("vitrine"));
  location.hash = i;
  count.textContent = `${i + 1} / ${slides.length}`;
}

function next() {
  const opening = slides[at].classList.contains("vitrine");
  if (opening && !slides[at].classList.contains("play")) { replay(slides[at]); return; }   // the first key starts it
  const frag = slides[at].querySelector(".frag:not(.on)");
  if (frag) {
    slides[at].querySelectorAll(".frag.live").forEach(f => f.classList.remove("live"));
    frag.classList.add("on", "live");
  } else if (at < slides.length - 1) show(at + 1, false);
}

function prev() {
  if (at > 0) show(at - 1, true);
}

// The video's cues: the sentence under the picture, and the card it lights, follow the playing time. A click on
// the picture plays or pauses it, as P does; if the browser refuses, its reason is written where the cue goes.
function toggle(video) {
  const cue = video.closest(".slide").querySelector(".cue");
  if (video.paused) {
    video.play().catch(e => { if (cue) cue.textContent = `The browser would not play it: ${e.message}`; });
  }
  else video.pause();
}
for (const video of document.querySelectorAll("video")) {
  const slide = video.closest(".slide");
  video.addEventListener("click", () => toggle(video));
  const dur = slide.querySelector(".dur");                     // the film's length beside it, from its metadata
  if (dur) {
    const length = () => {
      const s = Math.round(video.duration);
      if (s) dur.textContent = `${Math.floor(s / 60)}:${String(s % 60).padStart(2, "0")}`;
    };
    video.addEventListener("loadedmetadata", length);
    length();
  }
  const cue = slide.querySelector(".cue");
  if (!cue) continue;
  const cues = [...slide.querySelectorAll(".cues li")]
    .map(li => ({ at: Number(li.dataset.at), text: li.textContent, card: li.dataset.card }));
  video.addEventListener("timeupdate", () => {
    const passed = cues.filter(c => c.at <= video.currentTime);
    const last = passed[passed.length - 1];
    cue.textContent = last ? last.text : "";
    if (last && last.card) {
      const name = document.createElement("code");
      name.className = "named";
      name.textContent = last.card;
      cue.append(" ", name);
    }
    const lit = passed.filter(c => c.card).map(c => c.card);
    slide.querySelectorAll(".card[data-card]").forEach(card => {
      const on = lit.includes(card.dataset.card);
      card.classList.toggle("on", on);
      card.classList.toggle("live", on && card.dataset.card === lit[lit.length - 1]);
    });
  });
  video.addEventListener("ended", () => cue.classList.add("done"));
  video.addEventListener("play", () => cue.classList.remove("done"));
  video.addEventListener("error", () => {
    cue.textContent = `The browser could not load the video (${video.error ? video.error.message : "unknown"}).`;
  });
}

function tick() {
  if (!started) return;
  const s = (Date.now() - started) / 1000;
  bar.style.width = `${Math.min(100, s / (MINUTES * 60) * 100)}%`;
  bar.classList.toggle("over", s > MINUTES * 60);
  count.dataset.time = `${Math.floor(s / 60)}:${String(Math.floor(s % 60)).padStart(2, "0")}`;
  requestAnimationFrame(tick);
}

// The stage is 1600 x 900; scale it to the window and keep it centred. On the single page it is zoomed to the
// window's width instead, and every slide is on with its opening played out.
const stage = document.querySelector(".stage");
function fit() {
  if (all) { stage.style.setProperty("--z", innerWidth / 1600); return; }
  const s = Math.min(innerWidth / 1600, innerHeight / 900);
  stage.style.transform = `translate(-50%, -50%) scale(${s})`;
}
addEventListener("resize", fit);
if (all) {
  document.documentElement.classList.add("all");
  slides.forEach(s => { s.classList.add("on"); if (s.classList.contains("vitrine")) s.classList.add("play"); });
}
fit();

document.addEventListener("keydown", e => {
  if (all) return;                                             // the single page scrolls as any page does
  const video = slides[at].querySelector("video");
  const forward = e.key === "ArrowRight" || e.key === " " || e.key === "PageDown" || e.key === "ArrowDown";
  const back = e.key === "ArrowLeft" || e.key === "PageUp" || e.key === "ArrowUp";
  if (forward) { e.preventDefault(); next(); }
  else if (back) { e.preventDefault(); prev(); }
  else if (e.key === "n" || e.key === "N") document.body.classList.toggle("notes");
  else if ((e.key === "p" || e.key === "P") && video) toggle(video);
  else if ((e.key === "r" || e.key === "R") && video) { video.currentTime = 0; toggle(video); }
  else if ((e.key === "r" || e.key === "R") && slides[at].classList.contains("vitrine")) replay(slides[at]);
  else if (e.key === "s" || e.key === "S") {
    started = started ? 0 : Date.now(); bar.style.width = "0"; delete count.dataset.time; tick();
  }
  else if (e.key === "Home") show(0, false);
  else if (e.key === "End") show(slides.length - 1, true);
});
document.addEventListener("click", e => { if (!all && !e.target.closest("a, video")) next(); });
show(at, false);
