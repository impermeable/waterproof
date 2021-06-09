/* eslint-disable require-jsdoc */
/**
 * Abstract class representing a generic type returned by SerApi
 */
export default abstract class CoqType {
  // abstract pprint() : string; // TODO add parameter indent.
  pprint(indent = 0): string {
    const tab = '\n'.concat('\t'.repeat(indent));
    let output = tab.concat(`(${this.constructor.name})`, tab);
    output = output.concat('\t(%s)', tab);
    return output;
  }
  sprintf(format, ...args): string {
    let i = 0;
    return format.replace(/%s/g, function() {
      return args[i++];
    });
  }
  cprint(content, indent): string {
    const tab = '\n'.concat('\t'.repeat(indent+1));
    let output = 'Content: ';
    if (!Array.isArray(content)) {
      output = output.concat(content.pprint(indent+1), tab);
    } else {
      output = output.concat(tab, '\t', content.toString(), tab);
    }
    return output;
  }
}
