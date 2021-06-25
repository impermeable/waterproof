/* eslint-disable require-jsdoc */
import CApp from '../CApp';
import CLambdaN from '../CLambdaN';
import CLocalAssum from '../CLocalAssum';
import CNotation from '../CNotation';
import CoqAST from '../CoqAst';
import CoqType from '../CoqType';
import CPrim from '../CPrim';
import CProdN from '../CProdN';
import CRef from '../CRef';
import DefineBody from '../DefineBody';
import GenericVType from '../GenericVType';
import HintsResolve, {HintsReference} from '../HintsResolve';
import IDt from '../IDt';
import InConstrEntry from '../InConstrEntry';
import LocInfo from '../LocInfo';
import SerQualid from '../SerQualid';
import VernacAssumption from '../VernacAssumption';
import VernacDefinition from '../VernacDefinition';
import VernacEndProof from '../VernacEndProof';
import VernacExpr from '../VernacExpr';
import VernacExtend from '../VernacExtend';
import VernacHints from '../VernacHints';
import VernacProof from '../VernacProof';
import VernacRequire from '../VernacRequire';
import VernacStartTheoremProof from '../VernacStartTheoremProof';
import ASTVisitor from './ASTVisitor';


function sprintf(format, ...args): string {
  let i = 0;
  return format.replace(/%s/g, function() {
    return args[i++];
  });
}

class PrettyVisitor implements ASTVisitor {
  private INDENT_SIZE = 2;
  private _indent = 0;
  private _ppString = '%s';

  getSpace() {
    const n = this._indent * this.INDENT_SIZE;
    const space = ' '.repeat(n);
    return space;
  }

  formatTerm(term) {
    let r = `${this.getSpace}(${term.constructor.name}\n`;
    this._indent++;
    r += `${this.getSpace}(%s)\n`;
    this._indent--;
    r += `${this.getSpace})`;
    return r;
  }

  visitCoqAST(term: CoqAST): void {
    // throw new Error('Method not implemented.');
    this._ppString = sprintf(this.formatTerm(term),
        `Loc: (%s) %s`);
    this.visitLocInfo(term.locinfo);
  }
  visitGenericVType(term: GenericVType): void {
    throw new Error('Method not implemented.');
  }
  visitCoqType(term: CoqType): void {
    throw new Error('Method not implemented.');
  }
  visitCApp(term: CApp): void {
    throw new Error('Method not implemented.');
  }
  visitCLambdaN(term: CLambdaN): void {
    throw new Error('Method not implemented.');
  }
  visitCLocalAssum(term: CLocalAssum): void {
    throw new Error('Method not implemented.');
  }
  visitCNotation(term: CNotation): void {
    throw new Error('Method not implemented.');
  }
  visitCoqAst(term: CoqAST): void {
    throw new Error('Method not implemented.');
  }
  visitCPrim(term: CPrim): void {
    throw new Error('Method not implemented.');
  }
  visitCProdN(term: CProdN): void {
    throw new Error('Method not implemented.');
  }
  visitCRef(term: CRef): void {
    throw new Error('Method not implemented.');
  }
  visitDefineBody(term: DefineBody): void {
    throw new Error('Method not implemented.');
  }
  visitHintsResolve(term: HintsResolve): void {
    throw new Error('Method not implemented.');
  }
  visitHintsReference(term: HintsReference): void {
    throw new Error('Method not implemented.');
  }
  visitIDt(term: IDt): void {
    throw new Error('Method not implemented.');
  }
  visitInConstrEntry(term: InConstrEntry): void {
    throw new Error('Method not implemented.');
  }
  visitLocInfo(term: LocInfo): void {
    this._ppString = sprintf(this._ppString,
        `${this.getSpace}Start line ${term.line_nb}, pos `+
        `${term.bol_pos}` +
        `${this.getSpace}Eline ${term.line_nb_last}, ${term.bol_pos_last}`,
    );
  }
  visitSerQualid(term: SerQualid): void {
    throw new Error('Method not implemented.');
  }
  visitVernacDefinition(term: VernacDefinition): void {
    throw new Error('Method not implemented.');
  }
  visitVernacEndProof(term: VernacEndProof): void {
    throw new Error('Method not implemented.');
  }
  visitVernacExpr(term: VernacExpr): void {
    throw new Error('Method not implemented.');
  }
  visitVernacExtend(term: VernacExtend): void {
    throw new Error('Method not implemented.');
  }
  visitVernacHints(term: VernacHints): void {
    throw new Error('Method not implemented.');
  }
  visitVernacProof(term: VernacProof): void {
    throw new Error('Method not implemented.');
  }
  visitVernacRequire(term: VernacRequire): void {
    throw new Error('Method not implemented.');
  }
  visitVernacStartTheoremProof(term: VernacStartTheoremProof): void {
    throw new Error('Method not implemented.');
  }
  visitVernacAssumption(term: VernacAssumption): void {
    throw new Error('Method not implemented.');
  }

  public get(): string {
    return this._ppString;
  }
}

export function ppAST(ast: CoqType): string {
  const v = new PrettyVisitor();
  ast.accept(v);
  return v.get();
}

export default PrettyVisitor;
