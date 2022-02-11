const md = require('markdown-it')();
const mk = require('@iktakahiro/markdown-it-katex');
md.use(mk);

/**
 * Render text to html.
 * @param {string} text
 * @return {string} rendered text
 */
export function render(text) {
  // Replace coqdoc-style headers (*) with markdown headers (#)
  let converted = text.replace(/^[ ]*([*]+) /gm, (match, p1) => {
    return '#'.repeat(p1.length) + ' ';
  });
  // Replace coqdoc-style lists (-) with markdown lists (*)
  converted = converted.replace(/^([ ]*)- /gm, '$1* ');
  return md.render(converted);
}
