/* eslint-disable require-jsdoc */

import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';

class HintsResolve extends CoqType {
  hintList: any;
  constructor( array ) {
    super();
    this.hintList = array[1].map((el) => {
      return {
        info: el[0],
        bool: el[1] === 'true',
        refOrConstr: convertToASTComp(el[2]),
      };
    });
  }

  pprint(): string {
    throw new Error('Method not implemented.');
  }
}

export class HintsReference extends CoqType {
  locinfo: any;
  content: any;
  constructor( array ) {
    super();
    this.locinfo = new LocInfo(['loc', array[1].loc]);
    this.content = convertToASTComp(array[1].v);
  }

  pprint(indent = 0): string {
    const tab = '\n'.concat('\t'.repeat(indent+1));
    let output = '';
    output = output.concat('Loc: ', this.locinfo.pprint(indent+1), tab);
    output = output.concat(this.cprint(this.content, indent));
    return this.sprintf(super.pprint(indent), output);
  }
}

export default HintsResolve;
