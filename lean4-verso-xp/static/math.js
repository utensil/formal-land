const load_script = (src, onload) => {
    console.debug(`loading ${src}`)
    const script = document.createElement('script')
    // script.type = 'module'
    script.src = src
    script.setAttribute('onload', onload)
    document.head.appendChild(script)
}

const load_css = (href) => {
    console.debug(`loading ${href}`)
    const link = document.createElement('link')
    link.rel = 'stylesheet'
    link.href = href
    document.head.appendChild(link)
}

const render = () => {
    for (const m of document.querySelectorAll(".math.inline")) {
        katex.render(m.textContent, m, {throwOnError: false, displayMode: false});
    }
    for (const m of document.querySelectorAll(".math.display")) {
        katex.render(m.textContent, m, {throwOnError: false, displayMode: true});
    }
}

load_css('https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/katex.min.css')
load_script('https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/katex.min.js', 'render();')
// load_script('https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/contrib/auto-render.min.js', 'renderMathInElement(document.body);')
// https://github.com/leanprover/reference-manual/blob/main/static/math.js

// document.addEventListener("DOMContentLoaded", () => {

// });

