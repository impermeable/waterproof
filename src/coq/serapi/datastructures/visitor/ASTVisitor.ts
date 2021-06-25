/* eslint-disable semi */
import {CoqAST} from '../../ASTProcessor';
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
import TacReduce from '../TacReduce';
import TacticDefinition from '../TacticDefinition';

/**
 * Defines an interface the vistor pattern over ASTs
 * generated from SerApi - CoqTypes
 *
 * Gotchas: In JS you cannot do type-based overloading,
 * only paramater number-based; So we need diffrent function names
 * per each type we visit.
 */
interface ASTVisitor {
  visitCoqAst(term: CoqAST): void;
  visitGenericVType(term: GenericVType): void;
  visitCoqType(term: CoqType): void;
  visitCApp(term: CApp): void;
  visitCLambdaN(term: CLambdaN): void;
  visitCLocalAssum(term: CLocalAssum): void;
  visitCNotation(term: CNotation): void;
  visitCPrim(term: CPrim): void;
  visitCProdN(term: CProdN): void;
  visitCRef(term: CRef): void;
  visitDefineBody(term: DefineBody): void;
  visitHintsResolve(term: HintsResolve): void;
  visitHintsReference(term: HintsReference): void;
  visitIDt(term: IDt): void;
  visitInConstrEntry(term: InConstrEntry): void;
  visitLocInfo(term: LocInfo): void;
  visitSerQualid(term: SerQualid): void;
  visitVernacDefinition(term: VernacDefinition): void;
  visitVernacEndProof(term: VernacEndProof): void;
  visitVernacExpr(term: VernacExpr): void;
  visitVernacExtend(term: VernacExtend): void;
  visitVernacHints(term: VernacHints): void;
  visitVernacProof(term: VernacProof): void;
  visitVernacRequire(term: VernacRequire): void;
  visitVernacStartTheoremProof(term: VernacStartTheoremProof): void;
  visitVernacAssumption(term: VernacAssumption): void;
  visitVernacOpenCloseScope(term: VernacOpenCloseScope): void;
  visitTacAlias(term: TacAlias): void;
  visitKerName(term: KerName): void;
  visitTacAtom(term: TacAtom): void;
  visitTacApply(term: TacApply): void;
  visitTacReduce(term: TacReduce): void;
  visitTacticDefinition(term: TacticDefinition): void;
}

export default ASTVisitor;
