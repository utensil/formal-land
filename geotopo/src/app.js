"use strict";
const DATA = JSON.parse(document.getElementById("route-data").textContent);
const RM = DATA.roadmap, NODES = RM.nodes, GOALS = RM.routes;
/* The payload ships positional rows plus index tables (build.py: project()), which is
   what keeps the page small; decode once into the field names the rest of this file
   reads, so no rendering code below deals with the encoding. */
const IV = DATA.interned, PR_BASE = DATA.base.pr, HTERMS = DATA.health_terms;
const pull = (table, index) => index == null || index < 0 ? null : IV[table][index];
const decodePr = row => {
  const [number, title, state, created, merged, closed, labels, nodes, worked, reviewed, health, head, evidence, checks, events] = row;
  const [score, terms, failed, reason, source] = health;
  return {
    number, title, state: pull("state", state), url: PR_BASE + number, labels: labels.map(i => pull("workflow", i)), nodes,
    created_at: created, merged_at: merged, closed_at: closed, worked: !!worked, reviewed: !!reviewed, head,
    reviewEvidence: evidence,
    health: {score, terms: Object.fromEntries(HTERMS.map((k, i) => [k, terms[i]])),
             failed: failed.map(i => pull("rubric", i)), reason: pull("reason", reason), source},
    checks: checks.map(([name, status, conclusion, url]) => ({name: pull("check", name), status: pull("status", status), conclusion: pull("conclusion", conclusion), url})),
    events: events.map(([kind, at, label]) => ({kind: pull("kind", kind), at, label: pull("label", label)})),
  };
};
const PRS = DATA.prs.map(decodePr);
// These are the SpinRep route, node-state, activity and health palettes.
const PALETTE = ["#6d9cbe", "#6b8e23", "#cc7833", "#7570b3", "#a5c261", "#bc9458", "#da4939"];
const ST = {done:"landed / available", review:"in review", open:"future milestone", branch:"next handoff", incomplete:"partial / unfinished"};
const TL_STATE = {D:"#8fa3b8", R:"#6d9cbe", V:"#e5c07b", T:"#a5c261", M:"#7fb069", C:"#c97b7b"};
const TL_NAME = {D:"draft", R:"open / revision", V:"review", T:"ready to merge", M:"merged", C:"closed, unmerged"};
const byId = new Map(NODES.map(n => [n.id, n]));
const byPR = new Map(PRS.map(p => [p.number, p]));
const byEdge = new Map(RM.edges.map(e => [e.id, e]));
const routeNodes = new Map(GOALS.map(g => [g.id, new Set(g.edges.flatMap(id => {const e=byEdge.get(id);return [e.fromNode,e.toNode];}))]));
const state = {routes:new Set(GOALS.map(g=>g.id)), cohort:"all", node:null};
const $ = id => document.getElementById(id);
const esc = x => String(x ?? "").replace(/[&<>"']/g, c=>({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]));
const url = value => /^https:\/\/(github\.com|utensil\.github\.io)\//.test(value || "") ? value : "#";
const sourceLink = (value,label="source") => `<a href="${esc(url(value))}" target="_blank" rel="noopener">${esc(label)}</a>`;
const {dateTime, dayKey, floorSlot, nextSlot} = LocalTime;
const ms = value => new Date(value).getTime();
const shortTitle = p => p.title.replace(/^(?:feat|refactor|docs|chore)(?:\([^)]*\))?:\s*/, "");
function prLink(p) {return `<a class="prlink pr-${p.state === "merged" ? "merged" : p.state === "closed" ? "closed" : p.state === "draft" ? "draft" : "open"}${!p.worked && p.state === "merged" ? " pr-upstream" : ""}" href="${esc(url(p.url))}" target="_blank" rel="noopener">#${p.number}</a>`;}
const nodePrs = id => PRS.filter(p=>p.nodes.includes(id));
const goalPrs = g => PRS.filter(p=>p.nodes.some(id=>routeNodes.get(g.id).has(id)));
function nodeState(n) {
  const ps=nodePrs(n.id);
  if (!ps.length) return n.status;
  // A PR can contribute to a proof milestone without proving the summit theorem.
  if (n.kind === "proof") return n.status === "done" ? "done" : ps.some(p=>p.state === "open" || p.state === "draft") ? "review" : n.status;
  if (ps.some(p=>p.state === "open" || p.state === "draft")) return "review";
  if (ps.some(p=>p.state === "merged")) return "done";
  return "incomplete";
}
function visiblePrs() {return PRS.filter(p=>(p.worked || p.reviewed) && (state.cohort !== "worked" || p.worked) && (state.cohort !== "reviewed" || p.reviewed) && (state.routes.size === GOALS.length || GOALS.some(g=>state.routes.has(g.id) && p.nodes.some(n=>routeNodes.get(g.id).has(n)))));}
const band = value => value >= 75 ? "#7fb069" : value >= 60 ? "#e5c07b" : "#c97b7b";

function renderLegend() {
  $("legend").innerHTML = `<div class="legrow"><span>routes:</span>${GOALS.map(g=>`<button class="gl" data-g="${g.id}" aria-pressed="true" title="Toggle route ${esc(g.symbol)} and its chart cohort"><span class="sw" style="background:${PALETTE[g.color]}"></span>${esc(g.symbol)}</button>`).join("")}<span style="margin:0 10px">|</span><span class="st"><span style="width:13px;height:13px;border-radius:50%;border:1.2px solid #e6e1dc;margin-right:5px"></span>junction · routes meet</span><span style="margin:0 10px">|</span><span class="st"><span style="width:16px;height:16px;border-radius:50%;border:2.8px solid #e6e1dc;margin-right:5px"></span>summit</span></div><div class="legrow"><span>node state:</span>${Object.entries(ST).map(([key,label])=>`<span class="st"><span class="dot nodest-${key}"></span>${esc(label)}</span>`).join("")}<span style="margin:0 10px">|</span><span>PR activity:</span>${Object.entries(TL_NAME).map(([key,label])=>`<span class="st"><span class="dot" style="background:${TL_STATE[key]}"></span>${esc(label)}</span>`).join("")}</div>`;
  $("legend").querySelectorAll("[data-g]").forEach(el=>{
    el.addEventListener("click",()=>{state.routes.has(el.dataset.g) ? state.routes.delete(el.dataset.g) : state.routes.add(el.dataset.g);el.classList.toggle("off",!state.routes.has(el.dataset.g));el.setAttribute("aria-pressed",String(state.routes.has(el.dataset.g)));hideTip();refreshRoutes();renderCharts();});
    bindRouteHover(el,el.dataset.g);
  });
}
function checkpointState(cp) {
  const statuses=cp.nodes.map(id=>nodeState(byId.get(id)));
  return statuses.every(s=>s==="done") ? "done" : statuses.some(s=>s==="done"||s==="review"||s==="incomplete") ? "incomplete" : "open";
}
function treeEntries(root,path="0") {
  return [[path,root],...root.children.flatMap((child,i)=>treeEntries(child,`${path}.${i}`))];
}
function renderGoalTree(branch,path="0") {
  const kind=branch.children.length ? "" : byId.get(branch.nodes[0]).kind;
  const tag=({proof:"proof horizon",statement:"statement gate","open-conjecture":"open conjecture"})[kind]||"";
  return `<li><button class="tree-node" data-tree-path="${path}"><span class="tree-dot ${kind==="proof"?"tree-summit":""}" style="background:var(--${checkpointState(branch)})"></span><span>${esc(branch.label)}</span>${tag?`<small>${esc(tag)}</small>`:""}</button>${branch.children.length?`<ul>${branch.children.map((child,i)=>renderGoalTree(child,`${path}.${i}`)).join("")}</ul>`:""}</li>`;
}
function treeContent(branch) {
  return `<b>${esc(branch.label)}</b><div class="tstatus">${branch.children.length?"Shared work package":"Target branch"}</div><p>${branch.nodes.map(id=>`<button data-jump-node="${id}">${esc(byId.get(id).label)}</button> · ${esc(ST[nodeState(byId.get(id))])}`).join("<br>")}</p><div class="tstatus">Select a milestone to see its exact scope and dependencies on the map.</div>`;
}
function renderGoals() {
  $("goals").innerHTML = GOALS.map(g=>{
    const ps=goalPrs(g), met=g.checkpoints.filter(cp=>checkpointState(cp)==="done").length;
    return `<div class="goal" data-g="${g.id}" style="--gc:${PALETTE[g.color]}"><h3><span class="sw" style="background:${PALETTE[g.color]}"></span>Route ${esc(g.symbol)} — ${esc(g.title)}</h3><div class="bar checkpoints">${g.checkpoints.map((cp,i)=>`<button class="checkpoint" data-checkpoint="${i}" title="${esc(cp.label)}: ${esc(ST[checkpointState(cp)])}" aria-label="${esc(cp.label)} checkpoint: ${esc(ST[checkpointState(cp)])}" style="background:var(--${checkpointState(cp)})"></button>`).join("")}</div><div class="checkpoint-labels">${g.checkpoints.map(cp=>`<span>${esc(cp.label)}</span>`).join("")}</div><div class="pct">${met} / ${g.checkpoints.length} checkpoints met · checkpoints vary in difficulty</div><div class="route-lbl">route branches</div><div class="route-tree"><ul>${renderGoalTree(g.tree)}</ul></div><div class="work">Our footholds: ${ps.length?ps.map(prLink).join(" · "):"no selected PR yet"}</div><div class="eval">${esc(g.insight)}</div><div class="rdev"><b>Goal:</b> ${esc(g.finish)}</div><div class="rdev"><b>Next handoff:</b> ${g.frontier.map(id=>`${esc(byId.get(id).label)} <span class="status-${nodeState(byId.get(id))}">(${esc(ST[nodeState(byId.get(id))])})</span>`).join(" · ")}</div></div>`;
  }).join("");
  $("goals").querySelectorAll(".goal").forEach(el=>{
    bindRouteHover(el,el.dataset.g);
    const g=GOALS.find(g=>g.id===el.dataset.g);
    const branches=new Map(treeEntries(g.tree));
    chartBind(el,"[data-tree-path]",button=>treeContent(branches.get(button.dataset.treePath)));
    chartBind(el,"[data-checkpoint]",button=>{const cp=g.checkpoints[Number(button.dataset.checkpoint)];return `<b>${esc(g.symbol)} · ${esc(cp.label)}</b><div class="tstatus">${esc(ST[checkpointState(cp)])}</div><p>${cp.nodes.map(id=>`${esc(byId.get(id).label)}: ${esc(ST[nodeState(byId.get(id))])}`).join("<br>")}</p><div class="tstatus">Every listed milestone must be available. Merged PR counts do not complete a checkpoint.</div>`;});
  });
  $("goals").querySelectorAll("[data-node-link]").forEach(el=>el.addEventListener("click",()=>{hideTip();selectNode(el.dataset.nodeLink,true);}));
}

const W=1560, ROW=94, TOP=70, X0=370, X1=1450;
const H=TOP+(RM.rows.length-1)*ROW+85;
const positions=new Map();
RM.rows.forEach((row,r)=>{
  const nodes=NODES.filter(n=>n.row===row.id);
  nodes.forEach((n,i)=>positions.set(n.id,{x:n.x ?? (nodes.length===1 ? (X0+X1)/2 : X0+i*(X1-X0)/(nodes.length-1)),y:TOP+r*ROW}));
});
function edgePath(a,b,off=0) {
  const dx=b.x-a.x,dy=b.y-a.y,len=Math.hypot(dx,dy)||1,nx=-dy/len,ny=dx/len;
  const p={x:a.x+nx*off,y:a.y+ny*off},q={x:b.x+nx*off,y:b.y+ny*off};
  const mx=(p.x+q.x)/2,my=(p.y+q.y)/2,bend=Math.min(24,len*.12);
  // A long vertical edge bows around intermediate nodes instead of passing through them.
  if(Math.abs(dx)<20 && Math.abs(dy)>ROW*1.4)return `M${p.x},${p.y} C${p.x+85},${p.y+dy*.33} ${q.x+85},${p.y+dy*.67} ${q.x},${q.y}`;
  if (Math.abs(dy)<1) return `M${p.x},${p.y} C${p.x+dx*.3},${p.y+28+off} ${p.x+dx*.7},${q.y+28+off} ${q.x},${q.y}`;
  return `M${p.x},${p.y} C${mx-dy/len*bend},${my+dx/len*bend} ${mx+dy/len*bend},${my-dx/len*bend} ${q.x},${q.y}`;
}
function labelLines(label,max=24) {
  if(label.length<=max)return [label];
  const words=label.split(" "),lines=[""];
  words.forEach(word=>{if(lines[lines.length-1].length+word.length>max)lines.push(word);else lines[lines.length-1]+=(lines[lines.length-1]?" ":"")+word;});
  return lines;
}
function renderMap() {
  let html=`<title id="map-title">Geometric topology: contribution routes in the overall roadmap</title><desc id="map-desc">${NODES.length} milestone nodes across all eleven layers. Gray dependencies and four branching routes; select nodes for evidence.</desc>`;
  RM.rows.forEach((row,i)=>html+=`<text class="lrow" x="305" y="${TOP+i*ROW+6}" text-anchor="end" style="font-size:21px">${esc(row.label)}</text>`);
  RM.edges.forEach(e=>html+=`<path class="edge edge-dep" d="${edgePath(positions.get(e.fromNode),positions.get(e.toNode))}"><title>${esc(byId.get(e.fromNode).label)} → ${esc(byId.get(e.toNode).label)}</title></path>`);
  GOALS.forEach(g=>g.edges.forEach(id=>{
    const edge=byEdge.get(id),shared=GOALS.filter(other=>other.edges.includes(id)),off=(shared.indexOf(g)-(shared.length-1)/2)*5.5;
    html+=`<path class="edge edge-goal" data-goal="${g.id}" stroke="${PALETTE[g.color]}" d="${edgePath(positions.get(edge.fromNode),positions.get(edge.toNode),off)}"/>`;
  }));
  NODES.forEach(n=>{
    const p=positions.get(n.id),goals=GOALS.filter(g=>routeNodes.get(g.id).has(n.id)),summits=GOALS.filter(g=>g.summits.includes(n.id)),ps=nodePrs(n.id),lines=labelLines(n.label);
    html+=`<g class="node" data-id="${n.id}" data-goals="${goals.map(g=>g.id).join(" ")}" tabindex="0" role="button" aria-label="${esc(n.label)}; ${esc(ST[nodeState(n)])}; ${ps.length} tracked PRs">${summits.map(g=>`<circle class="summit-halo" r="25" cx="${p.x}" cy="${p.y}" fill="${PALETTE[g.color]}"/><circle r="18" cx="${p.x}" cy="${p.y}" fill="none" style="stroke:${PALETTE[g.color]};stroke-width:2.8"/>`).join("")}<circle class="main nodest-${nodeState(n)}" cx="${p.x}" cy="${p.y}" r="13"/>${goals.length>1?`<circle class="junction" r="4" cx="${p.x}" cy="${p.y}"/>`:""}${lines.map((line,i)=>`<text class="nl" x="${p.x}" y="${p.y-20-(lines.length-1-i)*18}" text-anchor="middle">${esc(line)}</text>`).join("")}${ps.length?`<text class="ownmark" x="${p.x}" y="${p.y+33}" text-anchor="middle">${ps.map(p=>`#${p.number}${p.reviewed?" ◌":""}`).join(" · ")}</text>`:""}</g>`;
  });
  $("map").setAttribute("viewBox",`0 0 ${W} ${H}`);$("map").innerHTML=html;
  $("map").querySelectorAll(".edge-goal").forEach(el=>bindRouteHover(el,el.dataset.goal));
  $("map").querySelectorAll(".node").forEach(el=>{
    el.addEventListener("mouseenter",()=>{lightRoutes((el.dataset.goals||"").split(" "));showTip(nodeContent(byId.get(el.dataset.id)),el);});
    el.addEventListener("mouseleave",()=>{lightRoutes([]);scheduleHide();});
    el.addEventListener("click",()=>{selectNode(el.dataset.id);showTip(nodeContent(byId.get(el.dataset.id)),el,true);});
    el.addEventListener("keydown",e=>{if(e.key==="Enter"||e.key===" "){e.preventDefault();selectNode(el.dataset.id);showTip(nodeContent(byId.get(el.dataset.id)),el,true);}});
  });
}
function nodeContent(n) {
  const ps=nodePrs(n.id),dependent=RM.edges.filter(e=>e.fromNode===n.id).map(e=>byId.get(e.toNode).label);
  return `<b>${esc(n.label)}</b><div class="tstatus">${esc(n.layer)} · ${esc(ST[nodeState(n)])}${n.kind?" · "+esc(({proof:"proof horizon",statement:"statement gate","open-conjecture":"open conjecture",infrastructure:"infrastructure"})[n.kind]):""}</div><p>${esc(n.summary)}</p>${ps.length?`<div class="tstatus">Our work: ${ps.map(p=>`${prLink(p)} · ${esc(p.state)}${p.reviewed?" · reviewed by us":""}`).join("<br>")}</div>`:`<div class="tstatus">Roadmap context · no selected PR</div>`}${n.remaining?`<p><strong>Handoff:</strong> ${esc(n.remaining)}</p>`:""}${dependent.length?`<div class="tstatus">Feeds: ${esc(dependent.join(" · "))}</div>`:""}<div class="tstatus">${sourceLink(n.source,"pinned roadmap")}</div>`;
}
function selectNode(id,scroll=false) {
  const n=byId.get(id);if(!n)return;
  state.node=id;$("map-detail").innerHTML=nodeContent(n);
  $("map").querySelectorAll(".node").forEach(el=>el.classList.toggle("selected",el.dataset.id===id));
  if(scroll){
    const target=$("map").querySelector(`.node[data-id="${id}"]`);
    const viewport=$("map").parentElement,box=target.getBoundingClientRect(),frame=viewport.getBoundingClientRect();
    viewport.scrollLeft+=box.left+box.width/2-frame.left-viewport.clientWidth/2;
    window.scrollBy({top:box.top+box.height/2-innerHeight/2,behavior:"instant"});
    target.focus({preventScroll:true});
  }
}
function lightRoutes(ids) {
  const active=new Set(ids.filter(id=>state.routes.has(id)));
  document.querySelectorAll(".edge-goal").forEach(el=>el.classList.toggle("lit",active.has(el.dataset.goal)));
  document.querySelectorAll(".goal").forEach(el=>el.classList.toggle("lit",active.has(el.dataset.g)));
}
function bindRouteHover(el,id) {el.addEventListener("mouseenter",()=>lightRoutes([id]));el.addEventListener("mouseleave",()=>lightRoutes([]));el.addEventListener("focus",()=>lightRoutes([id]));el.addEventListener("blur",()=>lightRoutes([]));}
function refreshRoutes() {
  document.querySelectorAll(".edge-goal").forEach(el=>el.style.display=state.routes.has(el.dataset.goal)?"":"none");
  document.querySelectorAll(".goal").forEach(el=>el.classList.toggle("off",!state.routes.has(el.dataset.g)));
  document.querySelectorAll(".node").forEach(el=>{const ids=el.dataset.goals.split(" ").filter(Boolean);el.classList.toggle("dim",ids.length>0&&!ids.some(id=>state.routes.has(id)));});
}

let hideTimer=null,pinned=false;
function hideTip(){pinned=false;$("tip").style.display="none";}
function scheduleHide(){clearTimeout(hideTimer);hideTimer=setTimeout(()=>{if(!pinned&&!$("tip").matches(":hover"))hideTip();},350);}
function showTip(html,target,pin=false) {
  if(pinned&&!pin)return;
  clearTimeout(hideTimer);pinned=pin;
  const tip=$("tip");tip.innerHTML=`<button class="close-tip" aria-label="Close details">×</button>${html}`;tip.style.display="block";
  tip.querySelector(".close-tip").addEventListener("click",hideTip);
  const r=target.getBoundingClientRect(),box=tip.getBoundingClientRect();
  tip.style.left=Math.max(10,Math.min(r.left+r.width/2-box.width/2,innerWidth-box.width-10))+"px";
  tip.style.top=Math.max(10,Math.min(r.bottom+8,innerHeight-box.height-10))+"px";
  tip.querySelectorAll("[data-jump-node]").forEach(button=>button.addEventListener("click",()=>{hideTip();selectNode(button.dataset.jumpNode,true);}));
  tip.querySelectorAll("[data-jump-pr]").forEach(button=>button.addEventListener("click",()=>{const p=byPR.get(Number(button.dataset.jumpPr));hideTip();selectNode(p.nodes[0],true);}));
}
$("tip").addEventListener("mouseenter",()=>clearTimeout(hideTimer));$("tip").addEventListener("mouseleave",scheduleHide);
document.addEventListener("keydown",e=>{if(e.key==="Escape")hideTip();});

function transitions(pr) {
  const firstDraftChange=pr.events.filter(e=>e.kind==="ready_for_review"||e.kind==="convert_to_draft").sort((a,b)=>ms(a.at)-ms(b.at))[0];
  const all=[{at:pr.created_at,state:firstDraftChange?.kind==="ready_for_review"?"D":"R",label:"opened"}];
  for(const e of pr.events) {
    let next=null;
    if(e.kind==="labeled") next=({"awaiting-CI":"R","awaiting-author":"R","awaiting-review":"V","review-in-progress":"V","ready-to-merge":"T"})[e.label];
    if(e.kind==="convert_to_draft")next="D";
    if(e.kind==="ready_for_review"||e.kind==="reopened")next="R";
    if(e.kind==="closed"&&!pr.merged_at)next="C";
    if(next)all.push({at:e.at,state:next,label:e.label||e.kind});
  }
  if(pr.merged_at)all.push({at:pr.merged_at,state:"M",label:"merged"});
  else if(pr.closed_at)all.push({at:pr.closed_at,state:"C",label:"closed"});
  const result=[];let last=null;
  all.sort((a,b)=>ms(a.at)-ms(b.at)).forEach(e=>{if(e.state!==last){result.push({...e,number:pr.number});last=e.state;}});
  return result;
}
const TRACKED=PRS.filter(p=>p.worked || p.reviewed);
const EVENTS=TRACKED.flatMap(transitions);
/* ================= windowed viewport over the local calendar history =================
   Both timelines draw a *window* of the history instead of the whole of it, with a
   minimap that carries the draggable window: this is the spin representations route
   map's interaction, kept on geotopo's own axis. The unit is a continuous local
   calendar day, so empty windows keep their width, day boundaries stay exact across
   daylight-saving changes, and the charts keep drawing their six-hour local windows.
   The viewBox width is pinned and the activity plot's height is fixed, so moving or
   resizing the window changes column widths and never heights. */
let currentVisible = [];
const median = a => { const s = a.slice().sort((x, y) => x - y); return s.length % 2 ? s[(s.length - 1) / 2] : (s[s.length / 2 - 1] + s[s.length / 2]) / 2; };
const WIN = (function () {
  const first = Math.min(...TRACKED.map(p => ms(p.created_at)));
  const dayStarts = [];
  for (let t = LocalTime.startOfDay(first); t <= LocalTime.startOfDay(ms(DATA.collected_at)); t = LocalTime.addDays(t, 1)) dayStarts.push(t);
  const indexOfDay = new Map(dayStarts.map((t, i) => [LocalTime.dayKey(t), i]));
  const DEFAULT_DAYS = 90;
  const state = {d0: Math.max(0, dayStarts.length - DEFAULT_DAYS), dn: Math.min(dayStarts.length, DEFAULT_DAYS)};
  const W = 1408, LEFT = 60, RIGHT = 1378;
  const atLatest = () => state.d0 + state.dn >= dayStarts.length;
  function clamp() {
    if (state.dn > dayStarts.length) state.dn = dayStarts.length;
    if (state.dn < 2) state.dn = 2;
    if (state.d0 > dayStarts.length - state.dn) state.d0 = dayStarts.length - state.dn;
    if (state.d0 < 0) state.d0 = 0;
  }
  function view() {
    clamp();
    const from = dayStarts[state.d0], to = LocalTime.addDays(dayStarts[state.d0 + state.dn - 1], 1);
    return {from, to, slots: LocalTime.slotsBetween(from, to - 1), days: state.dn};
  }
  let current = view();
  const xOf = t => LEFT + (t - current.from) / Math.max(1, current.to - current.from) * (RIGHT - LEFT);
  const slotWidth = t => Math.max(3, xOf(nextSlot(t)) - xOf(t) - 6);
  /* Day labels, thinned so 90 days of them do not collide; a label sits at the middle
     of its day, and the local calendar decides where the day starts. */
  function axis(baseline) {
    const step = Math.max(1, Math.ceil(current.days / 14));
    let html = "";
    for (let d = 0; d < current.days; d += step) {
      const start = LocalTime.addDays(current.from, d);
      const middle = (xOf(start) + xOf(LocalTime.addDays(start, 1))) / 2;
      html += `<text x="${middle.toFixed(1)}" y="${baseline + 17}" font-size="11" fill="#8a857e" text-anchor="middle">${LocalTime.dayKey(start).slice(5)}</text>`;
    }
    return html;
  }
  /* the minimap's colours: the same three-day centered median the health chart draws,
     over the whole tracked cohort so the minimap is a stable reference for every lens */
  const medianByDay = (() => {
    const byDay = {};
    TRACKED.filter(p => p.merged_at && p.health.score != null).forEach(p => {
      const key = LocalTime.dayKey(ms(p.merged_at));
      (byDay[key] = byDay[key] || []).push(p.health.score);
    });
    const out = {};
    dayStarts.forEach(t => {
      const values = [];
      for (let d = -1; d <= 1; d += 1) values.push(...(byDay[LocalTime.dayKey(LocalTime.addDays(t, d))] || []));
      if (values.length) out[LocalTime.dayKey(t)] = median(values);
    });
    return out;
  })();
  const eventsByDay = {};
  EVENTS.forEach(e => { const key = LocalTime.dayKey(ms(e.at)); eventsByDay[key] = (eventsByDay[key] || 0) + 1; });

  const MW = 1408, MH = 40, PADL = 54, PADR = 14;
  const UPD = (MW - PADL - PADR) / Math.max(1, dayStarts.length);
  const BARW = Math.max(1.4, UPD * 0.45);
  const mx = d => PADL + (d + 0.5) * UPD;
  let drag = null;
  function renderMini() {
    const host = $("prmini");
    if (!host) return;
    clamp();
    const barY = 4, barH = 26;
    const maxDay = Math.max(1, ...dayStarts.map(t => eventsByDay[LocalTime.dayKey(t)] || 0));
    let html = `<svg viewBox="0 0 ${MW} ${MH}" preserveAspectRatio="xMidYMin meet" role="img" aria-label="The whole history, one column per calendar day; drag the window">`;
    dayStarts.forEach((t, i) => {
      const key = LocalTime.dayKey(t), count = eventsByDay[key] || 0, health = medianByDay[key];
      const fill = health == null ? "#6f6f6f" : health >= 75 ? "#7fb069" : health >= 60 ? "#e5c07b" : "#c97b7b";
      const height = Math.max(2, count / maxDay * barH);
      html += `<rect x="${(mx(i) - BARW / 2).toFixed(1)}" y="${(barY + barH - height).toFixed(1)}" width="${BARW.toFixed(1)}" height="${height.toFixed(1)}" fill="${fill}" opacity=".9"/>`;
    });
    html += `<line x1="${PADL}" y1="${barY + barH + 2}" x2="${MW - PADR}" y2="${barY + barH + 2}" stroke="#3a3a3a"/>`;
    if (dayStarts.length) {
      html += `<text x="${PADL}" y="${MH - 1}" font-size="9" fill="#8a857e">${LocalTime.dayKey(dayStarts[0]).slice(5)}</text>`;
      html += `<text x="${MW - PADR}" y="${MH - 1}" font-size="9" fill="#8a857e" text-anchor="end">${LocalTime.dayKey(dayStarts[dayStarts.length - 1]).slice(5)}</text>`;
    }
    const rx0 = Math.max(PADL, mx(state.d0) - UPD / 2), rx1 = Math.min(MW - PADR, mx(state.d0 + state.dn - 1) + UPD / 2);
    html += `<g class="winbox">` +
      `<rect class="win" x="${rx0.toFixed(1)}" y="2" width="${Math.max(6, rx1 - rx0).toFixed(1)}" height="${MH - 6}" rx="3"/>` +
      `<rect class="grip" data-grip="l" x="${(rx0 - 5).toFixed(1)}" y="2" width="11" height="${MH - 6}"/>` +
      `<rect class="grip" data-grip="r" x="${(rx1 - 6).toFixed(1)}" y="2" width="11" height="${MH - 6}"/></g></svg>`;
    host.innerHTML = html;
    bindMini(host.querySelector("svg"));
    const caption = $("prwincap");
    if (caption) {
      const last = LocalTime.dayKey(LocalTime.addDays(current.from, current.days - 1));
      caption.textContent = `window ${LocalTime.dayKey(current.from)} → ${last} · ${current.days} of ${dayStarts.length} calendar days · ${current.slots.length} six-hour columns` + (atLatest() ? " · latest" : "");
    }
  }
  const dayAtPixel = (svg, clientX) => {
    const rect = svg.getBoundingClientRect();
    const x = (clientX - rect.left) / Math.max(1, rect.width) * MW;
    return Math.max(0, Math.min(dayStarts.length - 1, Math.floor((x - PADL) / UPD)));
  };
  function bindMini(svg) {
    svg.addEventListener("pointerdown", event => {
      const grip = event.target.closest(".grip"), onRect = event.target.closest(".win");
      let d = dayAtPixel(svg, event.clientX);
      const end0 = state.d0 + state.dn;
      if (grip && grip.dataset.grip === "l") drag = {mode: "l", end0: end0};
      else if (grip) drag = {mode: "r", d0: state.d0};
      else {
        if (!onRect) {
          const half = Math.floor(state.dn / 2);
          state.d0 = Math.max(0, Math.min(dayStarts.length - state.dn, d - half));
          d = dayAtPixel(svg, event.clientX);
        }
        drag = {mode: "pan", d0: d, d00: state.d0};
      }
      clamp(); renderAll(currentVisible); event.preventDefault();
    });
    svg.addEventListener("wheel", event => {
      event.preventDefault();
      if (event.shiftKey) state.dn = Math.max(2, Math.round(state.dn * (event.deltaY > 0 ? 1.15 : 1 / 1.15)));
      else state.d0 += event.deltaY > 0 || event.deltaX > 0 ? 1 : -1;
      clamp(); renderAll(currentVisible);
    }, {passive: false});
    svg.addEventListener("dblclick", reset);
  }
  /* The svg is replaced on every render and pointer capture is avoided, so real and
     synthetic input behave the same. */
  window.addEventListener("pointermove", event => {
    if (!drag) return;
    const svg = document.querySelector("#prmini svg");
    if (!svg) return;
    const d = dayAtPixel(svg, event.clientX);
    if (drag.mode === "pan") state.d0 = drag.d00 + (d - drag.d0);
    else if (drag.mode === "l") { state.d0 = d; state.dn = drag.end0 - d; }
    else state.dn = d - drag.d0 + 1;
    clamp(); renderAll(currentVisible);
  });
  window.addEventListener("pointerup", () => { drag = null; });
  window.addEventListener("pointercancel", () => { drag = null; });
  document.addEventListener("keydown", event => {
    if (/^(INPUT|TEXTAREA|SELECT)$/.test(event.target.tagName)) return;
    if (event.key === "ArrowLeft" || event.key === "ArrowRight") {
      state.d0 += (event.key === "ArrowLeft" ? -1 : 1) * (event.shiftKey ? 7 : 1);
      clamp(); renderAll(currentVisible); event.preventDefault();
    } else if (event.key === "Home") { state.d0 = 0; clamp(); renderAll(currentVisible); event.preventDefault(); }
    else if (event.key === "End") { state.d0 = dayStarts.length - state.dn; clamp(); renderAll(currentVisible); event.preventDefault(); }
  });
  function reset() { state.dn = Math.min(dayStarts.length, DEFAULT_DAYS); state.d0 = Math.max(0, dayStarts.length - state.dn); clamp(); renderAll(currentVisible); }
  function renderAll(visible) {
    current = view();
    renderActivity(visible);
    renderHealth(visible);
    renderMini();
  }
  return {W, LEFT, RIGHT, xOf, slotWidth, axis, view, state, dayStarts, renderAll, reset, DEFAULT_DAYS, atLatest,
          indexOfDay: t => indexOfDay.get(LocalTime.dayKey(ms(t)))};
})();
function chartBind(host, selector, content) {
  host.querySelectorAll(selector).forEach(el => {
    el.addEventListener("mouseenter", () => showTip(content(el), el)); el.addEventListener("mouseleave", scheduleHide);
    el.addEventListener("click", () => showTip(content(el), el, true));
    el.addEventListener("keydown", e => { if (e.key === "Enter" || e.key === " ") { e.preventDefault(); showTip(content(el), el, true); } });
  });
}
function renderActivity(visible) {
  const v = WIN.view();
  const ids = new Set(visible.map(p => p.number)), events = EVENTS.filter(e => ids.has(e.number));
  const groups = new Map(v.slots.map(t => [t, []]));
  events.forEach(e => { const t = floorSlot(ms(e.at)); if (groups.has(t)) groups.get(t).push(e); });
  const max = Math.max(1, ...[...groups.values()].map(a => a.length));
  /* a fixed plot height: tall windows shrink their stack instead of stretching the page */
  const PER = 9, CAP = 12, plot = CAP * PER, baseline = 34 + plot, H = baseline + 35;
  const unit = Math.min(PER, CAP * PER / max);
  let html = `<svg viewBox="0 0 ${WIN.W} ${H}" preserveAspectRatio="xMidYMin meet" role="img" aria-label="State transitions per six-hour local window">`;
  html += `<line x1="40" y1="${baseline}" x2="${WIN.RIGHT + 10}" y2="${baseline}" stroke="#444" stroke-dasharray="2 4"/>`;
  v.slots.forEach(t => {
    const es = groups.get(t);
    if (!es.length) return;
    const x = WIN.xOf(t) + 3, bw = WIN.slotWidth(t);
    let y = baseline;
    for (const st of ["D", "R", "V", "T", "M", "C"]) {
      const n = es.filter(e => e.state === st).length;
      if (n) { y -= n * unit; html += `<rect x="${x}" y="${y}" width="${bw}" height="${n * unit}" fill="${TL_STATE[st]}" opacity=".85"/>`; }
    }
    html += `<text x="${x + bw / 2}" y="${y - 6}" font-size="12" fill="#e6e1dc" text-anchor="middle" font-weight="700">${es.length}</text>`;
    html += `<g class="tlcol" data-slot="${t}" tabindex="0" role="button" aria-label="${esc(dateTime(t))}: ${es.length} transitions"><rect x="${x - 3}" y="${y - 20}" width="${bw + 6}" height="${baseline - y + 34}" fill="transparent"/></g>`;
  });
  html += WIN.axis(baseline) + "</svg>";
  $("prtl").innerHTML = html;
  chartBind($("prtl"), ".tlcol", el => {
    const t = Number(el.dataset.slot), es = groups.get(t);
    return `<b>${esc(dateTime(t))} → ${esc(dateTime(nextSlot(t)))}</b><div class="tstatus">${es.length} state transitions</div>${es.map(e => { const p = byPR.get(e.number); return `<div class="tstatus">${esc(dateTime(e.at))} · ${prLink(p)} → <span style="color:${TL_STATE[e.state]}">${TL_NAME[e.state]}</span><br>${esc(shortTitle(p))} · ${esc(e.label)}</div>`; }).join("")}`;
  });
  $("activity-note").textContent = `${visible.length} selected PRs · ${events.length} stage transitions in this window · six-hour local calendar windows (${LocalTime.zone}), starting at 00:00, 06:00, 12:00 and 18:00, on a continuous local calendar day axis. Empty windows retain their time width; daylight-saving changes alter elapsed window length. Consecutive duplicate stages are collapsed; commits and individual rubric verdicts are not stage transitions. Drag the window above, or use the arrow keys, to move it; Shift-arrows move a week, double-click resets it.`;
}
function checkSummary(p) {
  const checks=p.checks||[];
  if(!checks.length)return "No check runs recorded";
  const failed=checks.filter(c=>["failure","cancelled","timed_out","action_required","startup_failure","stale"].includes(c.conclusion));
  const pending=checks.filter(c=>c.status!=="completed");
  return `${checks.length} check runs · ${failed.length} failed/cancelled · ${pending.length} pending`;
}
function healthContent(p) {
  const h=p.health,t=p.merged_at||p.closed_at||DATA.collected_at,verb=p.merged_at?"Merged":p.closed_at?"Closed, unmerged":"Open at snapshot";
  return `<b>${prLink(p)} · ${esc(shortTitle(p))}</b><div class="tstatus">${verb} · ${esc(dateTime(t))}</div><div class="tstatus">${p.worked?"Worked on":p.reviewed?"Reviewed by us":"Roadmap history; no work/review attribution"}${p.reviewed?" · reviewed by us":""}</div><div class="tstatus">${h.score==null?`Health unscored: ${esc(h.reason)}`:`Health <strong style="color:${band(h.score)}">${h.score}</strong> · ${Object.entries(h.terms).map(([k,v])=>`${k}=${v??"?"}`).join(" · ")}`}</div><div class="tstatus">Observed non-green rubrics: ${esc(h.failed.join(", ")||"none")}</div><div class="tstatus">Workflow: ${esc(p.labels.filter(l=>!l.startsWith("roadmap/")).join(" · ")||"no workflow label")}</div><div class="tstatus">CI: ${esc(checkSummary(p))}${(p.checks||[]).filter(c=>c.conclusion==="failure").map(c=>" · "+sourceLink(c.url,c.name)).join("")}</div><div class="tstatus">Snapshot head: <code style="overflow-wrap:anywhere">${esc(p.head)}</code></div><div class="tstatus">${h.source?sourceLink(h.source,"exact-head scoreboard"):"No complete exact-head scoreboard"}${p.reviewEvidence.length?" · "+p.reviewEvidence.map(e=>sourceLink(e,"review evidence")).join(" · "):""}</div><div class="tstatus"><button data-jump-pr="${p.number}">Show contribution on the map</button></div>`;
}
function renderHealth(visible) {
  const v = WIN.view();
  const top=55,plot=130,baseline=top+plot,yOf=h=>baseline-h/100*plot;
  let html=`<svg viewBox="0 0 ${WIN.W} ${baseline+38}" preserveAspectRatio="xMidYMin meet" role="img" aria-label="Public-review churn score at merge, close or snapshot time">`;
  [0,25,50,75,100].forEach(h=>{const y=yOf(h);html+=`<line x1="40" y1="${y}" x2="${WIN.RIGHT+10}" y2="${y}" stroke="#333" stroke-width=".6"/><text x="32" y="${y+4}" font-size="11" fill="#8a857e" text-anchor="end">${h}</text>`;});
  const merged=visible.filter(p=>p.merged_at&&p.health.score!=null),days=[...new Set(merged.map(p=>LocalTime.startOfDay(ms(p.merged_at))))].sort((a,b)=>a-b);
  const med=days.map(start=>{const window=LocalTime.medianWindow(start),sample=merged.filter(p=>ms(p.merged_at)>=window.start&&ms(p.merged_at)<window.end);return {day:dayKey(start),t:window.at,h:median(sample.map(p=>p.health.score)),count:sample.length};});
  /* only the window is drawn; the medians themselves stay computed over the whole lens
     so the days at either edge keep their true three-day sample */
  const inWindow = t => t >= v.from && t < v.to;
  const shown = med.filter(p => inWindow(p.t));
  if(shown.length>1)html+=`<path d="${shown.map((p,i)=>`${i?"L":"M"}${WIN.xOf(p.t)},${yOf(p.h)}`).join(" ")}" fill="none" stroke="#cc7833" stroke-width="1.5" opacity=".85"/>`;
  med.forEach((p,i)=>{if(inWindow(p.t))html+=`<g class="median-mark" data-median="${i}" tabindex="0" role="button" aria-label="${p.day} rolling median ${p.h}"><circle cx="${WIN.xOf(p.t)}" cy="${yOf(p.h)}" r="2.5" fill="#cc7833"/><circle cx="${WIN.xOf(p.t)}" cy="${yOf(p.h)}" r="9" fill="transparent"/></g>`;});
  const lastMedian=med[med.length-1],snapshot=ms(DATA.collected_at);
  if(lastMedian && lastMedian.t<snapshot && lastMedian.t>=v.from && snapshot<=v.to) {
    const x=Math.min(WIN.xOf(snapshot),WIN.RIGHT),y=yOf(lastMedian.h);
    html+=`<g class="median-carry" tabindex="0" role="button" aria-label="Last available merged-PR median ${lastMedian.h} from ${lastMedian.day}, carried to snapshot"><path d="M${WIN.xOf(lastMedian.t)},${y} L${x},${y}" fill="none" stroke="#cc7833" stroke-width="1.5" stroke-dasharray="5 4"/><circle cx="${x}" cy="${y}" r="4" fill="#cc7833"/><circle cx="${x}" cy="${y}" r="10" fill="transparent"/><text x="${x-12}" y="${y+15}" text-anchor="end" fill="#cc7833" font-size="10">last median ${lastMedian.h}</text></g>`;
  }
  let unscored=0;
  visible.forEach(p=>{
    const t=ms(p.merged_at||p.closed_at||DATA.collected_at);
    if(!inWindow(t))return;
    const x=WIN.xOf(t),value=p.health.score,y=value==null?17+(unscored++%2)*17:yOf(value),r=5,color=value==null?"#e5c07b":band(value);
    let shape=p.state==="merged"?(p.worked?`<circle cx="${x}" cy="${y}" r="${r}" fill="${color}"/>`:`<rect x="${x-r}" y="${y-r}" width="${2*r}" height="${2*r}" fill="${color}"/>`):p.state==="closed"?`<path d="M${x} ${y-r} L${x+r} ${y} L${x} ${y+r} L${x-r} ${y} Z" fill="${color}"/>`:`<path d="M${x} ${y-r} L${x+r} ${y+r} L${x-r} ${y+r} Z" fill="${color}"/>`;
    if(p.reviewed)shape+=`<circle cx="${x}" cy="${y}" r="8.5" fill="none" stroke="#e6e1dc" stroke-width="1" stroke-dasharray="2 2"/>`;
    html+=`<g class="hp" data-pr="${p.number}" tabindex="0" role="button" aria-label="PR ${p.number}, ${esc(p.state)}, health ${value??"unscored"}">${shape}<circle cx="${x}" cy="${y}" r="12" fill="transparent"/><text x="${x-10}" y="${y-8}" text-anchor="end" fill="#9d9485" font-size="10">#${p.number}</text></g>`;
  });
  if(unscored)html+=`<text x="32" y="24" font-size="10" fill="#9d9485" text-anchor="end">n/a</text>`;
  html+=WIN.axis(baseline)+"</svg>";$("prhealth").innerHTML=html;
  chartBind($("prhealth"),".hp",el=>healthContent(byPR.get(Number(el.dataset.pr))));
  chartBind($("prhealth"),".median-mark",el=>{const p=med[Number(el.dataset.median)];return `<b>${p.day} · rolling median ${p.h}</b><div class="tstatus">${p.count} selected merged PRs in this local calendar day and its two adjacent days (${esc(LocalTime.zone)}). Unscored PRs are excluded. This summarizes the current PR lens; missing review evidence remains unscored.</div>`;});
  chartBind($("prhealth"),".median-carry",()=>`<b>Last available median ${lastMedian.h}</b><div class="tstatus">From ${lastMedian.day}: ${lastMedian.count} scored merged PRs in the centered three-day window (${esc(LocalTime.zone)}). The dashed line carries this value to the snapshot at ${esc(dateTime(snapshot))}; it is not a new daily measurement. Open, closed-unmerged and unscored PRs do not enter the merged-PR median.</div>`);
}
function renderCharts() {
  const visible=visiblePrs();currentVisible=visible;WIN.renderAll(visible);
  $("work-summary").textContent=`PR inventory · ${visible.length} / ${PRS.length} PRs in the current lens`;
  $("work-table").innerHTML=`<table><thead><tr><th>PR</th><th>Milestone</th><th>State / workflow</th><th>Our role</th><th>Health</th></tr></thead><tbody>${visible.map(p=>`<tr><td>${prLink(p)} · ${esc(shortTitle(p))}</td><td>${p.nodes.map(id=>esc(byId.get(id).label)).join(" · ") || "Not yet mapped"}</td><td>${esc(p.state)}<br>${esc(p.labels.filter(l=>!l.startsWith("roadmap/")).join(" · "))}<br>${esc(checkSummary(p))}</td><td>${p.worked?"worked on":""}${p.reviewed?" · reviewed":""}${!p.worked&&!p.reviewed?"No attribution recorded":""}</td><td>${p.health.score??"unscored"}</td></tr>`).join("")}</tbody></table>`;
}
renderLegend();renderGoals();renderMap();renderCharts();
$("cohort").addEventListener("change",e=>{state.cohort=e.target.value;hideTip();renderCharts();});
const mergedCount=TRACKED.filter(p=>p.state==="merged").length,closedCount=TRACKED.filter(p=>p.state==="closed").length;
$("stats").textContent=`${NODES.length} milestones · ${RM.edges.length} cited dependencies · ${TRACKED.length} attributed PRs: ${mergedCount} merged, ${TRACKED.length-mergedCount-closedCount} open, ${closedCount} closed · ${TRACKED.filter(p=>p.reviewed).length} with verified review coverage. ◌ marks reviewed contributions. Selected TCWORK/TCREVIEW PRs only; closed PRs remain in the timelines. Route chips narrow the charts to mapped milestones.`;
$("sources").innerHTML=`<p>${sourceLink(RM.roadmapUrl,"Pinned GeometricTopology roadmap")} · ${sourceLink(RM.reference,"SpinRep design reference")}</p><p>Roadmap context checked ${esc(dateTime(RM.contextAsOf))}; PR snapshot refreshed ${esc(dateTime(DATA.collected_at))}. Only PRs annotated with verified TCWORK work or TCREVIEW review are included in the timelines; closed PRs remain included. Milestone mapping and worked/reviewed attribution remain explicit annotations. The review marker records verified coverage of the PR, not authorship of every public rubric observation.</p><p>Unchanged terminal evidence is retained; changed terminal PRs are refreshed. Earlier overwritten review rounds cannot be reconstructed. Route filters show only verified mappings.</p><p>${esc(RM.horizonNote)}</p>`;
$("snapshot").innerHTML=`Snapshot ${esc(dateTime(DATA.collected_at))} · times and calendar windows in ${esc(LocalTime.zone)}; source timestamps UTC · ${sourceLink("https://github.com/utensil/formal-land/tree/main/geotopo","data and update instructions")} · standalone HTML; no network requests.`;
