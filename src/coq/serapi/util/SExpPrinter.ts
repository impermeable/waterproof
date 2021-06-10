/**
 * A basic pretty-printer for SExpressions
 * @param {string} sexp
 * @return {string}
 */
export default function pprint(sexp: string) {
  const parsedExp = parseExp(sexp);
  return prettify(parsedExp, '');
}

/**
 * Parses the s-expression into a nested array structure.
 * @param {string} sexp
 * @return {Array<Any>} nested array
 */
function parseExp(sexp: string) {
  const t = sexp.match(/\s*("[^"]*"|\(|\)|"|[^\s()"]+)/g);
  if (t === null) {
    return undefined;
  }
  let o =false;
  let c = 0;
  for (let i=t.length-1; i>=0; i--) {
    const n = t[i].trim();
    const ti = t[i].trim();
    if (ti === '"') return;
    else if (ti === '(') t[i]='[', c+=1;
    else if (ti === ')') t[i]=']', c-=1;
    else if (!isNaN(+ti)) {
      t[i]=n;
    } else t[i] = '\'' + ti.replace('\'', '\\\'') + '\'';
    if (i>0 && ti!=']' && t[i-1].trim()!='(' ) t.splice(i, 0, ',');
    if (!c) if (!o) o=true; else return;
  }
  const jstring = t.join('').replace(/,\]/g, ']').replace(/"/g, '\\"')
      .replace(/'/g, '"').replace(/(?:\r\n|\r|\n)/g, '\\n');

  if (c>0) {
    throw Error('Couldn\'t parse the whole input');
  }

  return JSON.parse(jstring);
}


/**
 *
 * @param {Array} arr
 * @param {string} spacer
 * @return {string} prettified expresion
 */
function prettify(arr: Array<any>, spacer: string) {
  if (!spacer) spacer = '';
  let r = spacer + '(\n';
  const e = arr.length;
  const indent = Array(4).join(' ');
  const s2 = spacer + indent;
  for (let i=0; i<e; i+=1) {
    const ai = arr[i];
    const sep = i === e-1 ? '\n' : '';
    const line = i === 0 ? s2+ai+sep : indent+ai+sep;
    r += ai.constructor !== Array ? line: prettify(ai, s2);
  }
  return r + spacer + ')\n';
}
