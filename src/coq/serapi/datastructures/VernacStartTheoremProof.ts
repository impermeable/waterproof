/* eslint-disable no-unused-vars */
import {convertToASTComp} from '../ASTProcessor';
import CoqType, {Visitable} from './CoqType';
import LocInfo from './LocInfo';
import ASTVisitor from './visitor/ASTVisitor';

enum TheoremKind {
  Theorem = 'Theorem',
  Lemma = 'Lemma',
  Fact = 'Fact',
  Remark = 'Remark',
  Property = 'Property',
  Proposition = 'Proposition',
  Corollary = 'Corollary',
}

// eslint-disable-next-line require-jsdoc
export default class VernacStartTheoremProof extends CoqType
  implements Visitable {
  theoremKind: TheoremKind;
  proofExprs: [any, any];

  // eslint-disable-next-line require-jsdoc
  constructor( array ) {
    super();
    this.theoremKind = array[1];

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

  // eslint-disable-next-line require-jsdoc
  accept(visitor: ASTVisitor): void {
    visitor.visitVernacStartTheoremProof(this);
  }
}
