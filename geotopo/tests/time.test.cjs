const assert = require("node:assert/strict");
const {execFileSync} = require("node:child_process");
const {test} = require("node:test");
const path = require("node:path");
const source = path.resolve(__dirname, "../src/time.js");

function inZone(zone, body) {
  execFileSync(process.execPath, ["-e", `
    const assert = require("node:assert/strict");
    const vm = require("node:vm");
    const context = {};
    vm.runInNewContext(require("node:fs").readFileSync(${JSON.stringify(source)}, "utf8") + ";globalThis.clock = LocalTime", context);
    const clock = context.clock;
    const iso = t => new Date(t).toISOString();
    ${body}
  `], {env: {...process.env, TZ: zone}, stdio: "pipe"});
}

test("the same UTC instant uses each browser's local day and six-hour bucket", () => {
  for (const [zone, day, start] of [
    ["UTC", "2026-09-13", "2026-09-13T00:00:00.000Z"],
    ["Asia/Singapore", "2026-09-13", "2026-09-12T22:00:00.000Z"],
    ["America/Los_Angeles", "2026-09-12", "2026-09-12T19:00:00.000Z"],
    ["Asia/Kathmandu", "2026-09-13", "2026-09-13T00:15:00.000Z"]
  ]) inZone(zone, `
    const t = Date.parse("2026-09-13T00:30:00Z");
    assert.equal(clock.dayKey(t), ${JSON.stringify(day)});
    assert.equal(iso(clock.floorSlot(t)), ${JSON.stringify(start)});
    assert.ok(clock.dateTime(t).includes(String(new Date(t).getHours()).padStart(2, "0") + ":30") || ${JSON.stringify(zone)} === "Asia/Kathmandu");
  `);
});

for (const [name, start, end, firstHours, windowHours] of [
  ["spring forward", "2026-03-08T05:00:00Z", "2026-03-09T04:00:00Z", 5, 71],
  ["fall back", "2026-11-01T04:00:00Z", "2026-11-02T05:00:00Z", 7, 73]
]) test(`local calendar buckets and median windows survive ${name}`, () => {
  inZone("America/New_York", `
    const start = Date.parse(${JSON.stringify(start)}), end = Date.parse(${JSON.stringify(end)});
    const slots = clock.slotsBetween(start, end - 1);
    assert.equal(slots.length, 4);
    assert.deepEqual(Array.from(slots, t => new Date(t).getHours()), [0, 6, 12, 18]);
    assert.equal((clock.nextSlot(start) - start) / 3600000, ${firstHours});
    assert.equal(clock.nextSlot(slots[3]), end);
    for (let t = start; t < end; t += 15 * 60000) {
      const bucket = clock.floorSlot(t);
      assert.ok(slots.includes(bucket));
      assert.ok(bucket <= t && t < clock.nextSlot(bucket));
    }
    const window = clock.medianWindow(start);
    assert.equal((window.end - window.start) / 3600000, ${windowHours});
    assert.equal(new Date(window.at).getHours(), 12);
  `);
});
