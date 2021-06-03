/* eslint-disable require-jsdoc */

import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';

export default class HintsResolve extends CoqType {
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

  pprint(): string {
    throw new Error('Method not implemented.');
  }
}
