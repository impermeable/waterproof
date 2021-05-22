import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';

// eslint-disable-next-line require-jsdoc
export default class VernacStartTheoremProof extends CoqType {
  theoremKind: any;
  proofExprs: never[];
  // TheoremKindEnum = {
  //   Theorem: 'Theorem',
  //   Lemma: 'Lemma',
  //   Fact: 'Fact',
  //   Remark: 'Remark',
  //   Property: 'Property',
  //   Proposition: 'Proposition',
  //   Corollary: 'Corollary',
  // }

  // eslint-disable-next-line require-jsdoc
  constructor( array ) {
    super();
    this.theoremKind = array[1];
    // console.log
    this.proofExprs = [];
    this.proofExprs = array[2][0].map((el) => {
      const id = el[0];
      const exprList = el[1];
      const l1 = Object.keys(id).length;
      const l2 = Object.keys(exprList).length;

      const result = {};
      if (l1 > 1) {
        if (id.v) {
          const ident = id.v[0] === 'Id' ? id.v[1] : undefined;
          result['ident_decl'] = {
            locinfo: new LocInfo(['loc', id.loc]),
            ident: ident,
          };
        } else {
          // console.warn('TODO: PARSE', id);
          result['unparsed'] = id.map((i) => convertToASTComp(i));
        }
      }
      if (l2 > 0) {
        result['data'] = {
          locinfo: new LocInfo(['loc', exprList.loc]),
          content: convertToASTComp(exprList.v),
        };
      }
      return result;
    });
  }

  // eslint-disable-next-line require-jsdoc
  pprint(): string {
    throw new Error('Method not implemented.');
  }
}
