/* eslint-disable require-jsdoc */
import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';

export default class CLocalAssum extends CoqType {
  names: any;
  binderKind: any;
  expr: { locinfo: LocInfo; content: any; };

  constructor( array ) {
    super();
    console.warn('CLocalAssum', array);
    this.names = array[1].map((name) => ({
      locinfo: new LocInfo(['loc', name.loc]),
      content: convertToASTComp(name.v),
    }));
    this.binderKind = array[2];
    this.expr = {
      locinfo: new LocInfo(['loc', array[3].loc]),
      content: convertToASTComp(array[3].v),
    };
  }

  pprint(): string {
    throw new Error('Method not implemented.');
  }
}
