/* eslint-disable require-jsdoc */
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

type LocData = [LocInfo, string];

class FlattenVisitor implements ASTVisitor {
  private _state : LocData[] = [];

  visitCoqAST(term: CoqAst): void {
    // throw new Error('Method not implemented.');
    this._state.push([term.locinfo, term.constructor.name]);
  }

  visitCoqType(term: CoqType): void {
    const className = term.constructor.name;
    throw new Error(`Method not implemented for type of ${className}.`);
  }

  visitGenericVType(term: GenericVType): void {
    console.log(`Skippping term ${term.constructor.name}.`);
  }

  visitCApp(term: CApp): void {
    // throw new Error('Method not implemented.');
    this._state.push([term.first.expr.locinfo, term.constructor.name]);
  }

  visitCLambdaN(term: CLambdaN): void {
    this._state.push([term.expr.locinfo, term.constructor.name]);
  }

  visitCLocalAssum(term: CLocalAssum): void {
    this._state.push([term.expr.locinfo, term.constructor.name]);
  }

  visitCNotation(term: CNotation): void {
    // no LocInfo present
  }

  visitCoqAst(term: CoqAst): void {
    throw new Error('Method not implemented.');
  }

  visitCPrim(term: CPrim): void {
    // no locinfo
  }
  visitCProdN(term: CProdN): void {
    this._state.push([term.expr.locinfo, term.constructor.name]);
  }
  visitCRef(term: CRef): void {
    this._state.push([term.libNames.locinfo, term.constructor.name]);
  }
  visitDefineBody(term: DefineBody): void {
    this._state.push([term.expr.locinfo, term.constructor.name]);
  }

  visitHintsResolve(term: HintsResolve): void {
    //
  }
  visitHintsReference(term: HintsReference): void {
    this._state.push([term.locinfo, term.constructor.name]);
  }

  visitVernacAssumption(term: VernacAssumption): void {
    // No location info, so let it be
  }

  visitIDt(term: IDt): void {
    throw new Error('Method not implemented.');
  }
  visitInConstrEntry(term: InConstrEntry): void {
    throw new Error('Method not implemented.');
  }
  visitLocInfo(term: LocInfo): void {
    throw new Error('Method not implemented.');
  }
  visitSerQualid(term: SerQualid): void {
    throw new Error('Method not implemented.');
  }
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

  visitVernacEndProof(term: VernacEndProof): void {
    // can be empty
    // console.log('vEndproof', term);
    // throw Error(term);
  }

  visitVernacExpr(term: VernacExpr): void {
    throw new Error('Method not implemented.');
  }

  visitVernacExtend(term: VernacExtend): void {
    // TODO handle VernacExtend
  }

  visitVernacHints(term: VernacHints): void {
    // Doesn't have a location, ignore.
  }

  visitVernacProof(term: VernacProof): void {
    // console.log('Visit vernac proof is empty, skipping', term);
  }

  visitVernacRequire(term: VernacRequire): void {
    term.list.forEach((i) => {
      this._state.push([i.locinfo, i.content.id]);
    });
  }

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

  public get(): LocData[] {
    return this._state;
  }
}

export default FlattenVisitor;

export function flattenAST(ast: CoqType) : [LocInfo, string][] {
  const visitor = new FlattenVisitor();
  ast.accept(visitor);
  return visitor.get();
}
