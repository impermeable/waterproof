import CoqType, {Visitable} from './CoqType';
import ASTVisitor from './visitor/ASTVisitor';

/**
 * Class to represent a Coq VernacEndProof
 * @see https://coq.github.io/doc/v8.10/api/coq/Vernacexpr/index.html#type-proof_end
 * proofEnd =
 *  | Admitted
 *  | Proved
 */
class VernacEndProof extends CoqType implements Visitable {
  proofEnd: string;
  proofDetails: { isOpaque: boolean; lident: CoqType; } =
    {isOpaque: false, lident: {} as CoqType};
  proofFinished: boolean;

  /**
   * Parses an input array into a proper datastructure.
   * @param {Array} array: Array to parse
   */
  constructor( array: [string, string] | [string, [string, string, CoqType]] ) {
    super();
    if (typeof array[1] === 'string') {
      this.proofEnd = array[1];
    } else {
      this.proofEnd = array[1][0];
      this.proofDetails = {
        isOpaque: array[1][1] === 'Opaque',
        lident: array[1][2],
      };
    }
    this.proofFinished = this.proofEnd === 'Proved';
  }

  // eslint-disable-next-line valid-jsdoc
  /**
   * Returns a nice pretty-printed expression of {VernacEndProof}
   * TODO: fixme
   * @return {string}
   */
  pprint(indent = 0): string {
    const tab = '\n'.concat('\t'.repeat(indent + 1));
    let output = '';
    if (typeof this.proofEnd === 'string') {
      output = output.concat(this.proofEnd, tab);
    } else {
      output = output.concat(this.proofEnd, tab);
      output = output.concat('Details: ', this.proofDetails.isOpaque.toString(),
          tab);
    }
    output = output.concat('Finished: ', this.proofFinished.toString(), tab);
    return this.sprintf(super.pprint(indent), output);
  }

  // eslint-disable-next-line require-jsdoc
  accept(visitor: ASTVisitor): void {
    visitor.visitVernacEndProof(this);
  }
}

export default VernacEndProof;
