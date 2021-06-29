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

/**
 * A JavaScript equivalent of a Coq VernacStartTheoremProof object.
 * @see https://coq.github.io/doc/v8.12/api/coq/Vernacexpr/index.html#type-vernac_expr.VernacStartTheoremProof
 */
class VernacStartTheoremProof extends CoqType
  implements Visitable {
  theoremKind: TheoremKind;
  proofExprs: any[];

  /**
   * Constructor for VeracStartTheoremProof type.
   * @param {array} array Array to parse
   */
  constructor( array ) {
    super(array);
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

  /**
   * Pretty print the current type.
   * @param {number} indent current indentation
   * @return {string} representation of the current type with indentation
   * added to the front
   */
  pprint(indent = 0): string {
    const tab = '\n'.concat('\t'.repeat(indent + 1));
    let output = '';
    output = output.concat('Kind: ', this.theoremKind.toString(), tab);
    for (let i = 0; i < this.proofExprs.length; i++) {
      if (!this.proofExprs[i]['ident_decl'] === null) {
        output = output.concat('Loc: ',
            this.proofExprs[i]['ident_decl'].locinfo.pprint(indent+1), tab);
        output = output.concat(this.cprint(
            this.proofExprs[i]['ident_decl'].content, indent));
      }
      if (!this.proofExprs[i]['unparsed'] === null) {
        output = output.concat('Unparsed: ');
      }
      for (let j = 0; j < this.proofExprs[i]['unparsed']; j++) {
        output = output.concat(this.cprint(this.proofExprs[i]['unparsed'][j],
            indent+1));
      }
      if (!this.proofExprs[i]['data'] === null) {
        output = output.concat('Loc: ',
            this.proofExprs[i]['data'].locinfo.pprint(indent+1), tab);
        output = output.concat(
            this.cprint(this.proofExprs[i]['data'].content, indent));
      }
    }
    return this.sprintf(super.pprint(indent), output);
  }

  /**
   * Allows an ASTVisitor to traverse the current type
   * (part of the visitor pattern)
   * @param {ASTVisitor} visitor the visitor requiring
   * access to content of the current type
   */
  accept(visitor: ASTVisitor): void {
    visitor.visitVernacStartTheoremProof(this);
  }
}

/* istanbul ignore next */
export default VernacStartTheoremProof;
