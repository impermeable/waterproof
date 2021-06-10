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
import HintsResolve from '../HintsResolve';
import IDt from '../IDt';
import InConstrEntry from '../InConstrEntry';
import LocInfo from '../LocInfo';
import SerQualid from '../SerQualid';
import VernacDefinition from '../VernacDefinition';
import VernacEndProof from '../VernacEndProof';
import VernacExpr from '../VernacExpr';
import VernacExtend from '../VernacExtend';
import VernacHints from '../VernacHints';
import VernacProof from '../VernacProof';
import VernacRequire from '../VernacRequire';
import VernacStartTheoremProof from '../VernacStartTheoremProof';
// import CApp from '../CApp';
// import CLambdaN from '../CLambdaN';
// import CLocalAssum from '../CLocalAssum';

/**
 * Implements the vistor pattern.
 *
 * Gotchas: In JS you cannot do type-based overloading,
 * only paramater number-based; So we need diffrent function names
 * per each type we visit.
 */
interface ASTVisitor {
  visitCoqAST(term: CoqAST): void;
  visitGenericVType(term: GenericVType): void;
  visitCoqType(term: CoqType): void;
  visitCApp(term: CApp): void;
  visitCLambdaN(term: CLambdaN): void;
  visitCLocalAssum(term: CLocalAssum): void;
  visitCNotation(term: CNotation): void;
  visitCoqAst(term: CoqAst): void;
  visitCPrim(term: CPrim): void;
  visitCProdN(term: CProdN): void;
  visitCRef(term: CRef): void;
  visitDefineBody(term: DefineBody): void;
  visitHintsResolve(term: HintsResolve): void;
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
}

export default ASTVisitor;
// Note to self: quick hack to get all classes in a folder
// eslint-disable-next-line max-len
// ls src/coq/serapi/datastructures/**.ts | sed 's/\.[a-z]*//g' | awk -F '/' '{print $NF}'
