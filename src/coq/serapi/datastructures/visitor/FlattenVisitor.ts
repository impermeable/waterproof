import CApp from '../CApp';
import CLambdaN from '../CLambdaN';
import CLocalAssum from '../CLocalAssum';
import CNotation from '../CNotation';
import CoqAst from '../CoqAst';
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
import VernacOpenCloseScope from '../VernacOpenCloseScope';
import VernacAssumption from '../VernacAssumption';
import VernacDefinition from '../VernacDefinition';
import VernacEndProof from '../VernacEndProof';
import VernacExpr from '../VernacExpr';
import VernacExtend from '../VernacExtend';
import VernacHints from '../VernacHints';
import VernacProof from '../VernacProof';
import VernacRequire from '../VernacRequire';
import VernacStartTheoremProof from '../VernacStartTheoremProof';
import TacAlias from '../TacAlias';
import KerName from '../KerName';
import TacAtom from '../TacAtom';
import TacApply from '../TacApply';
import ASTVisitor from './ASTVisitor';

type LocData = [LocInfo, string];

/**
 * The FlattenVisitor class visits a CoqAST and returns
 * an array of {LocData} information.
 * This includes the string and the LocInfo provided by each type.
 */
class FlattenVisitor implements ASTVisitor {
  private _state : LocData[] = [];

  /**
   * Visit a CoqAST type.
   * @param {CoqAst} term a CoqAST type
   */
  visitCoqAst(term: CoqAst): void {
    this._state.push([term.locinfo, term.constructor.name]);
  }

  /**
   * Visit a CoqAST type.
   * @param {CoqAst} term - a CoqAST term
   */
  visitCoqType(term: CoqType): void {
    const className = term.constructor.name;
    throw new Error(`Method not implemented for type of ${className}.`);
  }

  /**
   * Visit a GenericVType type.
   * @param {GenericVType} term - a GenericVType term
   */
  visitGenericVType(term: GenericVType): void {
    console.log(`Skippping term ${term.constructor.name}.`);
  }

  /**
   * Visit a CApp type.
   * @param {CApp} term - a CApp term
   */
  visitCApp(term: CApp): void {
    this._state.push([term.first.expr.locinfo, term.constructor.name]);
  }

  /**
   * Visit a CLambdaN type.
   * @param {CLambdaN} term - a CLambdaN term
   */
  visitCLambdaN(term: CLambdaN): void {
    this._state.push([term.expr.locinfo, term.constructor.name]);
  }

  /**
   * Visit a CLocalAssum type.
   * @param {CLocalAssum} term - a CLocalAssum term
   */
  visitCLocalAssum(term: CLocalAssum): void {
    this._state.push([term.expr.locinfo, term.constructor.name]);
  }

  /**
   * Visit a CNotation type.
   * @param {CNotation} term - a CNotation term
   */
  visitCNotation(term: CNotation): void {
    // no LocInfo present, skipping
    console.log(`${term.constructor.name} has no LocInfo present. Skipping...`);
  }

  /**
   * Visit a CPrim type.
   * @param {CPrim} term - a CPrim term
   */
  visitCPrim(term: CPrim): void {
    // no LocInfo present, skipping
    console.log(`${term.constructor.name} has no LocInfo present. Skipping...`);
  }

  /**
   * Visit a CProdN type.
   * @param {CProdN} term - a CProdN term
   */
  visitCProdN(term: CProdN): void {
    this._state.push([term.expr.locinfo, term.constructor.name]);
  }

  /**
   * Visit a CRef type.
   * @param {CRef} term - a CRef term
   */
  visitCRef(term: CRef): void {
    this._state.push([term.libNames.locinfo, term.constructor.name]);
  }

  /**
   * Visit a DefineBody type.
   * @param {DefineBody} term - a DefineBody term
   */
  visitDefineBody(term: DefineBody): void {
    this._state.push([term.expr.locinfo, term.constructor.name]);
  }

  /**
   * Visit a HintsResolve type.
   * @param {HintsResolve} term - a HintsResolve term
   */
  visitHintsResolve(term: HintsResolve): void {
    // no LocInfo present, skipping
  }

  /**
   * Visit a HintsReference type.
   * @param {HintsReference} term - a HintsReference term
   */
  visitHintsReference(term: HintsReference): void {
    this._state.push([term.locinfo, term.constructor.name]);
  }

  /**
   * Visit a HintsReference type.
   * @param {VernacAssumption} term - a VernacAssumption term
   */
  visitVernacAssumption(term: VernacAssumption): void {
    // no LocInfo present, skipping
    console.log(`${term.constructor.name} has no LocInfo present. Skipping...`);
  }


  // eslint-disable-next-line require-jsdoc
  visitVernacOpenCloseScope(term: VernacOpenCloseScope): void {
    // No location info
  }

  /**
   * Visit a HintsReference type.
   * @param {VernacAssumption} term - a VernacAssumption term
   */
  visitTacAlias(term: TacAlias): void {
    this._state.push([term.locinfo, term.constructor.name]);
  }

  // eslint-disable-next-line require-jsdoc
  visitKerName(term: KerName): void {
    // No location info
  }

  // eslint-disable-next-line require-jsdoc
  visitTacAtom(term: TacAtom): void {
    console.log('tacatom');
    this._state.push([term.locinfo, term.constructor.name]);
  }

  // eslint-disable-next-line require-jsdoc
  visitTacApply(term: TacApply): void {
    this._state.push([term.locinfo, term.constructor.name]);
  }

  /**
   * Visit a IDt type.
   * @param {IDt} term - a IDt term
   */
  visitIDt(term: IDt): void {
    throw new Error('Method not implemented.');
  }

  /**
   * Visit a InConstrEntry type.
   * @param {InConstrEntry} term - a InConstrEntry term
   */
  visitInConstrEntry(term: InConstrEntry): void {
    throw new Error('Method not implemented.');
  }

  /**
   * Visit a LocInfo type.
   * @param {LocInfo} term - a LocInfo term
   */
  visitLocInfo(term: LocInfo): void {
    throw new Error('Method not implemented.');
  }

  /**
   * Visit a SerQualid type.
   * @param {SerQualid} term - a SerQualid term
   */
  visitSerQualid(term: SerQualid): void {
    throw new Error('Method not implemented.');
  }

  /**
   * Visit a VernacDefinition type.
   * @param {VernacDefinition} term - a VernacDefinition term
   */
  visitVernacDefinition(term: VernacDefinition): void {
    // throw new Error('Method not implemented.');
    console.warn(VernacDefinition.name, term);

    this._state.push([term.nameDecl.name.locinfo,
      term.nameDecl.name.content.constructor.name]);

    const defExpr = term.defitionExpr.expr;

    if (defExpr != null) {
      this._state.push([defExpr.locinfo,
        defExpr?.content.constructor.name]);
    }

    if (defExpr?.content.expr != null) {
      this._state.push([defExpr?.content.expr.locinfo,
        defExpr?.content.expr.content.constructor.name]);
    }
  }

  /**
   * Visit a VernacEndProof type.
   * @param {VernacEndProof} term - a VernacEndProof term
   */
  visitVernacEndProof(term: VernacEndProof): void {
    // can be empty
    // console.log('vEndproof', term);
    // throw Error(term);
  }

  /**
   * Visit a VernacExpr type.
   * @param {VernacExpr} term - a VernacExpr term
   */
  visitVernacExpr(term: VernacExpr): void {
    throw new Error('Method not implemented.');
  }

  /**
   * Visit a VernacExtend type.
   * @param {VernacExtend} term - a VernacExtend term
   */
  visitVernacExtend(term: VernacExtend): void {
    // TODO handle VernacExtend
  }

  /**
   * Visit a VernacHints type.
   * @param {VernacHints} term - a VernacHints term
   */
  visitVernacHints(term: VernacHints): void {
    // Doesn't have a location, ignore.
  }

  /**
   * Visit a VernacProof type.
   * @param {VernacProof} term - a VernacProof term
   */
  visitVernacProof(term: VernacProof): void {
    // console.log('Visit vernac proof is empty, skipping', term);
  }

  /**
   * Visit a VernacRequire type.
   * @param {VernacRequire} term - a VernacRequire term
   */
  visitVernacRequire(term: VernacRequire): void {
    term.list.forEach((i) => {
      this._state.push([i.locinfo, i.content.id]);
    });
  }

  /**
   * Visit a VernacStartTheoremProof type.
   * @param {VernacStartTheoremProof} term - a VernacStartTheoremProof term
   */
  visitVernacStartTheoremProof(term: VernacStartTheoremProof): void {
    // throw new Error('Method not implemented.');
    const {proofExprs} = term;
    this._state.push([proofExprs[0]?.ident_decl.locinfo,
      proofExprs[0]?.ident_decl.ident]);
    if ( proofExprs[1]?.data != null) {
      this._state.push([proofExprs[1]?.data.locinfo,
        proofExprs[1]?.data.content.constructor.name]);
    }
  }

  /**
   * Access the location data extracted by
   * the FlattenVisitor.
   * @return {LocData[]} an array of location data.
   */
  public get(): LocData[] {
    return this._state;
  }
}

export default FlattenVisitor;

/**
 * Wrapper function to easily obtain the
 * result of an AST flattning.
 * @param {CoqType} ast - a type inheriting from CoqType.
 * @return {[LocInfo,string][]} an array containing location info
 * and a string identifier
 */
export function flattenAST(ast: CoqType) : [LocInfo, string][] {
  const visitor = new FlattenVisitor();
  ast.accept(visitor);
  return visitor.get();
}
