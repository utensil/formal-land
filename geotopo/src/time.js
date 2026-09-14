"use strict";
// Input instants stay UTC. Calendar boundaries and labels use the browser zone.
const LocalTime = (() => {
  const zone = Intl.DateTimeFormat().resolvedOptions().timeZone;
  const formatter = new Intl.DateTimeFormat("en-GB", {
    day: "2-digit", month: "short", hour: "2-digit", minute: "2-digit",
    hour12: false, timeZoneName: "short"
  });
  const pad = n => String(n).padStart(2, "0");
  const dayKey = t => {
    const d = new Date(t);
    return `${d.getFullYear()}-${pad(d.getMonth() + 1)}-${pad(d.getDate())}`;
  };
  const startOfDay = t => {
    const d = new Date(t);
    d.setHours(0, 0, 0, 0);
    return d.getTime();
  };
  const addDays = (t, count) => {
    const d = new Date(t);
    d.setDate(d.getDate() + count);
    return d.getTime();
  };
  const floorSlot = t => {
    const d = new Date(t);
    d.setHours(Math.floor(d.getHours() / 6) * 6, 0, 0, 0);
    return d.getTime();
  };
  const nextSlot = t => {
    const d = new Date(t);
    d.setHours(d.getHours() + 6, 0, 0, 0);
    return d.getTime();
  };
  const slotsBetween = (start, end) => {
    const result = [];
    for (let t = floorSlot(start); t <= floorSlot(end); t = nextSlot(t)) result.push(t);
    return result;
  };
  const medianWindow = t => {
    const start = startOfDay(t), noon = new Date(start);
    noon.setHours(12);
    return {start: addDays(start, -1), end: addDays(start, 2), at: noon.getTime()};
  };
  return {zone, dateTime: t => formatter.format(new Date(t)), dayKey, startOfDay,
    addDays, floorSlot, nextSlot, slotsBetween, medianWindow};
})();
