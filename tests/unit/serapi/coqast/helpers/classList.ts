/* eslint-disable max-len */
import {CoqAST} from '../../../../../src/coq/serapi/ASTProcessor';
import CApp from '../../../../../src/coq/serapi/datastructures/CApp';
import CLambdaN from '../../../../../src/coq/serapi/datastructures/CLambdaN';
import CLocalAssum from
  '../../../../../src/coq/serapi/datastructures/CLocalAssum';
import CNotation from '../../../../../src/coq/serapi/datastructures/CNotation';
// import Co/qType from '../../../../../src/coq/serapi/datastructures/CoqType';
import CPrim from '../../../../../src/coq/serapi/datastructures/CPrim';
import CProdN from '../../../../../src/coq/serapi/datastructures/CProdN';
import CRef from '../../../../../src/coq/serapi/datastructures/CRef';
import DefineBody from
  '../../../../../src/coq/serapi/datastructures/DefineBody';
import GenericVType from
  '../../../../../src/coq/serapi/datastructures/GenericVType';
import HintsResolve, {HintsReference} from
  '../../../../../src/coq/serapi/datastructures/HintsResolve';
import IDt from '../../../../../src/coq/serapi/datastructures/IDt';
import InConstrEntry from
  '../../../../../src/coq/serapi/datastructures/InConstrEntry';
import IntroIdentifier from '../../../../../src/coq/serapi/datastructures/IntroIdentifier';
import IntroNaming from '../../../../../src/coq/serapi/datastructures/IntroNaming';
import KerName from '../../../../../src/coq/serapi/datastructures/KerName';
import SerQualid from '../../../../../src/coq/serapi/datastructures/SerQualid';
import TacAlias from '../../../../../src/coq/serapi/datastructures/TacAlias';
import TacApply from '../../../../../src/coq/serapi/datastructures/TacApply';
import TacArg from '../../../../../src/coq/serapi/datastructures/TacArg';
import TacAtom from '../../../../../src/coq/serapi/datastructures/TacAtom';
import TacCall from '../../../../../src/coq/serapi/datastructures/TacCall';
import TacFun from '../../../../../src/coq/serapi/datastructures/TacFun';
import TacIntroPattern from '../../../../../src/coq/serapi/datastructures/TacIntroPattern';
import TacReduce from '../../../../../src/coq/serapi/datastructures/TacReduce';
import TacRewrite from '../../../../../src/coq/serapi/datastructures/TacRewrite';
import TacThen from '../../../../../src/coq/serapi/datastructures/TacThen';
import TacticDefinition from '../../../../../src/coq/serapi/datastructures/TacticDefinition';
import VernacAssumption from '../../../../../src/coq/serapi/datastructures/VernacAssumption';
import VernacDefinition from
  '../../../../../src/coq/serapi/datastructures/VernacDefinition';
import VernacEndProof from
  '../../../../../src/coq/serapi/datastructures/VernacEndProof';
import VernacExpr from
  '../../../../../src/coq/serapi/datastructures/VernacExpr';
import VernacExtend from
  '../../../../../src/coq/serapi/datastructures/VernacExtend';
import VernacHints from
  '../../../../../src/coq/serapi/datastructures/VernacHints';
import VernacOpenCloseScope from '../../../../../src/coq/serapi/datastructures/VernacOpenCloseScope';
import VernacProof from
  '../../../../../src/coq/serapi/datastructures/VernacProof';
import VernacRequire from
  '../../../../../src/coq/serapi/datastructures/VernacRequire';
import VernacStartTheoremProof from
  '../../../../../src/coq/serapi/datastructures/VernacStartTheoremProof';

const empty = ['Empty', []];
const baseLoc = [[
  ['fname', 'ToplevelInput'], ['line_nb', 0], ['bol_pos', 0],
  ['line_nb_last', 0], ['bol_pos_last', 0], ['bp', 0], ['ep', 0]]];

export const coqTypes = {
  'CApp': {
    badIn: [],
    class: CApp,
    goodIn: ['CApp', ['', {loc: baseLoc, v: empty}], []],
    pprint: '\n(CApp)\n\t(Project flag: \n\tLoc: \n\t(LocInfo)\n\t\t(Name: ToplevelInput\n\t\tStart line: 0\n\t\tStart pos: 0\n\t\tEnd line: 0\n\t\tEnd pos: 0\n\t\tBp: 0\n\t\tEp: 0\n\t\t)\n\t\n\tContent: \n\t\tEmpty,)\n',
  },
  'CLambdaN': {
    badIn: [],
    class: CLambdaN,
    goodIn: ['CLambdaN', [], {loc: baseLoc, v: empty}],
    pprint: '\n(CLambdaN)\n\t(Loc: \n\t(LocInfo)\n\t\t(Name: ToplevelInput\n\t\tStart line: 0\n\t\tStart pos: 0\n\t\tEnd line: 0\n\t\tEnd pos: 0\n\t\tBp: 0\n\t\tEp: 0\n\t\t)\n\t\n\tContent: \n\t\tEmpty,)\n',
  },
  'CLocalAssum': {
    badIn: [],
    class: CLocalAssum,
    goodIn: ['CLocalAssum', [], [], {loc: baseLoc, v: empty}],
    pprint: '\n(CLocalAssum)\n\t(Kind: \n\tLoc: \n\t(LocInfo)\n\t\t(Name: ToplevelInput\n\t\tStart line: 0\n\t\tStart pos: 0\n\t\tEnd line: 0\n\t\tEnd pos: 0\n\t\tBp: 0\n\t\tEp: 0\n\t\t)\n\t\n\tContent: \n\t\tEmpty,)\n',
  },
  'CNotation': {
    badIn: [],
    class: CNotation,
    goodIn: ['CNotation', '', empty, [[], [], [], []]],
    pprint: '\n(CNotation)\n\t(Content: \n\t\tEmpty,)\n',
  },
  'CoqAst': {
    badIn: [],
    class: CoqAST,
    goodIn: ['CoqAST', [empty, ['loc', baseLoc]]],
    pprint: '\n(CoqAST)\n\t(Loc: \n\t(LocInfo)\n\t\t(Name: ToplevelInput\n\t\tStart line: 0\n\t\tStart pos: 0\n\t\tEnd line: 0\n\t\tEnd pos: 0\n\t\tBp: 0\n\t\tEp: 0\n\t\t)\n\t\n\tContent: \n\t\tEmpty,)\n',
  },
  'CPrim': {
    badIn: [],
    class: CPrim,
    goodIn: ['CPrim', ['Numeric', ['data', {exp: 0, frac: 1, int: 3}]]],
    pprint: '\n(CPrim)\n\t(Is numeric: true\n\t\tPositive: false\n\t\tExp: 0\n\t\tFrac: 1\n\t\tInt: 3\n\t)\n',
  },
  'CProdN': {
    badIn: [],
    class: CProdN,
    goodIn: ['CProdN', [empty, empty], {loc: baseLoc, v: empty}],
    pprint: '\n(CProdN)\n\t(Loc: \n\t(LocInfo)\n\t\t(Name: ToplevelInput\n\t\tStart line: 0\n\t\tStart pos: 0\n\t\tEnd line: 0\n\t\tEnd pos: 0\n\t\tBp: 0\n\t\tEp: 0\n\t\t)\n\t\n\tContent: \n\t\tEmpty,)\n',
  },
  'CRef': {
    badIn: [],
    class: CRef,
    goodIn: ['CRef', {loc: baseLoc, v: empty}, {}],
    pprint: '\n(CRef)\n\t(Loc: \n\t(LocInfo)\n\t\t(Name: ToplevelInput\n\t\tStart line: 0\n\t\tStart pos: 0\n\t\tEnd line: 0\n\t\tEnd pos: 0\n\t\tBp: 0\n\t\tEp: 0\n\t\t)\n\t\n\tContent: \n\t\tEmpty,Instance: [object Object]\n\t)\n',
  },
  'DefineBody': {
    badIn: [],
    class: DefineBody,
    goodIn: ['DefineBody', [], [], {loc: baseLoc, v: empty}, []],
    pprint: '\n(DefineBody)\n\t(Local expr: \n\tRed exp: \n\tLoc: \n\t(LocInfo)\n\t\t(Name: ToplevelInput\n\t\tStart line: 0\n\t\tStart pos: 0\n\t\tEnd line: 0\n\t\tEnd pos: 0\n\t\tBp: 0\n\t\tEp: 0\n\t\t)\n\t\n\tContent: \n\t\tEmpty,Expr option: \n\t)\n',
  },
  'GenericVType': {
    badIn: [],
    class: GenericVType,
    goodIn: ['v', [['attrs', 2], ['control', '4'], ['expr', empty]]],
    pprint: '',
  },
  'HintsReference': {
    badIn: [],
    class: HintsReference,
    goodIn: ['HintsReference', {loc: baseLoc, v: empty}],
    pprint: '\n(HintsReference)\n\t(Loc: \n\t(LocInfo)\n\t\t(Name: ToplevelInput\n\t\tStart line: 0\n\t\tStart pos: 0\n\t\tEnd line: 0\n\t\tEnd pos: 0\n\t\tBp: 0\n\t\tEp: 0\n\t\t)\n\t\n\tContent: \n\t\tEmpty,)\n',
  },
  'HintsResolve': {
    badIn: [],
    class: HintsResolve,
    goodIn: ['HintsResolve', []],
    pprint: '\n(HintsResolve)\n\t()\n',
  },
  'IDt': {
    badIn: [],
    class: IDt,
    goodIn: ['IDt', 'Special'],
    pprint: '\n(IDt)\n\t(Name: Special\n\t)\n',
  },
  'InConstrEntry': {
    badIn: [],
    class: InConstrEntry,
    goodIn: [],
    pprint: '\n(InConstrEntry)\n\t()\n',
  },
  'IntroIdentifier': {
    badIn: [],
    class: IntroIdentifier,
    goodIn: ['IntroIdentifier', ['value', 'Special']],
    pprint: '\n(IntroIdentifier)\n\t(Id: Special\n\t)\n',
  },
  'IntroNaming': {
    badIn: [],
    class: IntroNaming,
    goodIn: ['IntroNaming', [empty]],
    pprint: '\n(IntroNaming)\n\t(Content: \n\t\tEmpty,)\n',
  },
  'KerName': {
    badIn: [],
    class: KerName,
    goodIn: ['KerName', '', ['', 'Id_With_Spaces#Type']],
    pprint: '\n(KerName)\n\t(Id: Type\n\tType: Id With Spaces\n\t)\n',
  },
  'Ser_Qualid': {
    badIn: [],
    class: SerQualid,
    goodIn: ['Ser_Qualid', ['', ''], ['', 12]],
    pprint: '\n(SerQualid)\n\t(Path: \n\tId: 12\n\t)\n',
  },
  'TacAlias': {
    badIn: [],
    class: TacAlias,
    goodIn: ['TacAlias', {loc: [baseLoc], v: [empty]}],
    pprint: '\n(TacAlias)\n\t(Loc: \n\t(LocInfo)\n\t\t(Name: ToplevelInput\n\t\tStart line: 0\n\t\tStart pos: 0\n\t\tEnd line: 0\n\t\tEnd pos: 0\n\t\tBp: 0\n\t\tEp: 0\n\t\t)\n\t\n\tContent: \n\t\tEmpty,)\n',
  },
  'TacApply': {
    badIn: [],
    class: TacApply,
    goodIn: ['TacApply', true, true, [['', [{loc: baseLoc, v: empty}]]]],
    pprint: '\n(TacApply)\n\t(Loc: \n\t(LocInfo)\n\t\t(Name: ToplevelInput\n\t\tStart line: 0\n\t\tStart pos: 0\n\t\tEnd line: 0\n\t\tEnd pos: 0\n\t\tBp: 0\n\t\tEp: 0\n\t\t)\n\t\n\tContent: \n\t\tEmpty,)\n',
  },
  'TacArg': {
    badIn: [],
    class: TacArg,
    goodIn: ['TacArg', {loc: [baseLoc], v: [empty]}],
    pprint: '\n(TacArg)\n\t(Loc: \n\t(LocInfo)\n\t\t(Name: ToplevelInput\n\t\tStart line: 0\n\t\tStart pos: 0\n\t\tEnd line: 0\n\t\tEnd pos: 0\n\t\tBp: 0\n\t\tEp: 0\n\t\t)\n\tContent: \n\t\tEmpty,)\n',
  },
  'TacAtom': {
    badIn: [],
    class: TacAtom,
    goodIn: ['TacAtom', {loc: [baseLoc], v: empty}],
    pprint: '\n(TacAtom)\n\t(Loc: \n\t(LocInfo)\n\t\t(Name: ToplevelInput\n\t\tStart line: 0\n\t\tStart pos: 0\n\t\tEnd line: 0\n\t\tEnd pos: 0\n\t\tBp: 0\n\t\tEp: 0\n\t\t)\n\t\n\tContent: \n\t\tEmpty,)\n',
  },
  'TacCall': {
    badIn: [],
    class: TacCall,
    goodIn: ['TacCall', {'loc': [baseLoc, baseLoc], 'v': [{'v': empty}, {'v': empty}]}],
    pprint: '\n(TacCall)\n\t(Loc: \n\t(LocInfo)\n\t\t(Name: ToplevelInput\n\t\tStart line: 0\n\t\tStart pos: 0\n\t\tEnd line: 0\n\t\tEnd pos: 0\n\t\tBp: 0\n\t\tEp: 0\n\t\t)\n\tContent: \n\t\tEmpty,)\n',
  },
  'TacFun': {
    badIn: [],
    class: TacFun,
    goodIn: ['TacFun', [{'Name': [1, 2]}, []]],
    pprint: '\n(TacFun)\n\t(Name: 2\n\tContent: \n\t\t)\n',
  },
  'TacIntroPattern': {
    badIn: [],
    class: TacIntroPattern,
    goodIn: ['TacIntroPattern', [], []],
    pprint: '\n(TacIntroPattern)\n\t()\n',
  },
  'TacReduce': {
    badIn: [],
    class: TacReduce,
    goodIn: ['TacReduce', ['Type', {AllOccurrences: {loc: [baseLoc], v: ['', {v: empty}]}}]],
    pprint: '\n(TacReduce)\n\t(Type: Type\n\tLoc: \n\t(LocInfo)\n\t\t(Name: ToplevelInput\n\t\tStart line: 0\n\t\tStart pos: 0\n\t\tEnd line: 0\n\t\tEnd pos: 0\n\t\tBp: 0\n\t\tEp: 0\n\t\t)\n\t\n\tContent: \n\t\tEmpty,)\n',
  },
  'TacRewrite': {
    badIn: [],
    class: TacRewrite,
    goodIn: ['TacRewrite', '', [['', '', ['', [{loc: [baseLoc], v: empty}]]]]],
    pprint: '\n(TacRewrite)\n\t(Loc: \n\t(LocInfo)\n\t\t(Name: ToplevelInput\n\t\tStart line: 0\n\t\tStart pos: 0\n\t\tEnd line: 0\n\t\tEnd pos: 0\n\t\tBp: 0\n\t\tEp: 0\n\t\t)\n\tContent: \n\t\tEmpty,)\n',
  },
  'TacThen': {
    badIn: [],
    class: TacThen,
    goodIn: ['TacThen', ['', empty]],
    pprint: '\n(TacThen)\n\t(Content: \n\t\t,Empty,)\n',
  },
  'TacticDefinition': {
    badIn: [],
    class: TacticDefinition,
    goodIn: ['TactidDefinition', {v: ['empty', empty], loc: [baseLoc]}, empty],
    pprint: '\n(TacticDefinition)\n\t(Type: Empty,\n\tLoc: \n\t(LocInfo)\n\t\t(Name: ToplevelInput\n\t\tStart line: 0\n\t\tStart pos: 0\n\t\tEnd line: 0\n\t\tEnd pos: 0\n\t\tBp: 0\n\t\tEp: 0\n\t\t)\n\t\n\tContent: \n\t\tEmpty,)\n',
  },
  'v': {
    badIn: [],
    class: GenericVType,
    goodIn: ['v', [['attrs', 1], ['control', ''], ['expr', empty]]],
    pprint: '',
  },
  'VernacAssumption': {
    badIn: [],
    class: VernacAssumption,
    goodIn: ['VernacAssumption', 'discharge', 'inline'],
    pprint: '\n(VernacAssumption)\n\t(Discharge: discharge\n\tInline: inline\n\t)\n',
  },
  'VernacOpenCloseScope': {
    badIn: [],
    class: VernacOpenCloseScope,
    goodIn: ['VernacOpenCloseScope', 'true', 'scope.AST.testing'],
    pprint: '\n(VernacOpenCloseScope)\n\t(Open: true\n\tScope: scope.AST.testing\n\t)\n',
  },
  'VernacDefinition': {
    badIn: [],
    class: VernacDefinition,
    goodIn: ['VernacDefinition', ['DoDischarge', ''], [{
      loc: baseLoc,
      v: empty,
    }, []], empty],
    pprint: '\n(VernacDefinition)\n\t(Discharge: true\n\tDef: \n\tName: \n\t\tLoc: \n\t\t(LocInfo)\n\t\t\t(Name: ToplevelInput\n\t\t\tStart line: 0\n\t\t\tStart pos: 0\n\t\t\tEnd line: 0\n\t\t\tEnd pos: 0\n\t\t\tBp: 0\n\t\t\tEp: 0\n\t\t\t)\n\t\t\n\t\tContent: \n\t\t\t\tEmpty,)\n',
  },
  'VernacEndProof': {
    badIn: [],
    class: VernacEndProof,
    goodIn: ['Proved', ''],
    pprint: '\n(VernacEndProof)\n\t(\n\tFinished: false\n\t)\n',
  },
  'VernacExpr': {
    badIn: [],
    class: VernacExpr,
    goodIn: ['VernacExpr', '', empty],
    pprint: '\n(VernacExpr)\n\t()\n',
  },
  'VernacExtend': {
    badIn: [],
    class: VernacExtend,
    goodIn: ['VernacExtend', '', [[[], [], [], [['', empty, [empty]]]]]],
    pprint: '\n(VernacExtend)\n\t(Content: \n\t\t,Empty,,Empty,)\n',
  },
  'VernacHints': {
    badIn: [],
    class: VernacHints,
    goodIn: ['VernacHints', '', empty],
    pprint: '\n(VernacHints)\n\t(Strings: \n\tHint: \n\t\tEmpty,\n\t)\n',
  },
  'VernacProof': {
    badIn: [],
    class: VernacProof,
    goodIn: [],
    pprint: '\n(VernacProof)\n\t(Arg: [object Object]\n\tExpr: [object Object]\n\t)\n',
  },
  'VernacRequire': {
    badIn: [],
    class: VernacRequire,
    goodIn: ['VernacRequire', '121', 'false', []],
    pprint: '\n(VernacRequire)\n\t(Qualid: 121\n\tFlag: false\n\t)\n',
  },
  'VernacStartTheoremProof': {
    badIn: [],
    class: VernacStartTheoremProof,
    goodIn: ['VernacStartTheoremProof', 'Lemma', [[[{'v': ['Id', 'example_reflexivity'], 'loc': [{'fname': 'ToplevelInput', 'line_nb': 5, 'bol_pos': 105, 'line_nb_last': 5, 'bol_pos_last': 105, 'bp': 153, 'ep': 172}]}, {}], [{}, {'v': empty, 'loc': [{'fname': 'ToplevelInput', 'line_nb': 6, 'bol_pos': 175, 'line_nb_last': 6, 'bol_pos_last': 175, 'bp': 177, 'ep': 182}]}]]]],
    pprint: '\n(VernacStartTheoremProof)\n\t(Kind: Lemma\n\t)\n',
  },
};

export const withLocInfo = {
  'CoqAst': {
    class: CoqAST,
    data: ['CoqAst', [['VernacExtend', '', ''], ['loc', baseLoc]]],
  },
  'CApp': {
    class: CApp,
    data: ['CApp', ['', {loc: baseLoc, v: empty}], []],
  },
  'CLambdaN': {
    class: CLambdaN,
    data: ['CLambdaN', [], {loc: baseLoc, v: empty}],
  },
  'CLocalAssum': {
    class: CLocalAssum,
    data: ['CLocalAssum', [], [], {loc: baseLoc, v: empty}],
  },
  'CProdN': {
    class: CProdN,
    data: ['CProdN', [empty, empty], {loc: baseLoc, v: empty}],
  },
  'CRef': {
    class: CRef,
    data: ['CRef', {loc: baseLoc, v: empty}, {}],
  },
  'HintsReference': {
    class: HintsReference,
    data: ['HintsReference', {loc: baseLoc, v: ['VernacExtend', '', '']}],
  },
  'VernacDefinition': {
    class: VernacDefinition,
    data: ['VernacDefinition', ['DoDischarge', ''], [{loc: baseLoc, v: empty},
      []], empty],
    skip: true,
  },
  'DefineBody': {
    class: DefineBody,
    data: ['DefineBody', [], [], {loc: baseLoc, v: empty}, []],
  },
  'TacCall': {
    class: TacCall,
    data: ['TacCall', {'loc': [baseLoc, baseLoc], 'v': [{'v': empty}, {'v': empty}]}],
  },
  'VernacStartTheoremProof': {
    class: VernacStartTheoremProof,
    data: ['VernacStartTheoremProof', 'Lemma', [[[{'v': ['Id', 'example_reflexivity'], 'loc': [{'fname': 'ToplevelInput', 'line_nb': 0, 'bol_pos': 0, 'line_nb_last': 0, 'bol_pos_last': 0, 'bp': 0, 'ep': 0}]}, {}], [{}, {'v': [], 'loc': [{'fname': 'ToplevelInput', 'line_nb': 0, 'bol_pos': 0, 'line_nb_last': 0, 'bol_pos_last': 0, 'bp': 0, 'ep': 0}]}]]]],
    count: 2,
    skip: true,
  },
  'TacAlias': {
    class: TacAlias,
    data: ['TacAlias', {loc: [baseLoc], v: [empty]}],
  },
  'TacApply': {
    class: TacApply,
    data: ['TacApply', true, true, [['', [{loc: baseLoc, v: empty}]]]],
  },
  'TacAtom': {
    class: TacAtom,
    data: ['TacAtom', {loc: [baseLoc], v: empty}],
  },
  'TacticDefinition': {
    class: TacticDefinition,
    data: ['TactidDefinition', {v: ['empty', empty], loc: [baseLoc]}, empty],
  },
};

const coqTypesKeys = Object.keys(coqTypes);
const locInfoKeys = Object.keys(withLocInfo);

export const woLocInfoKeys = coqTypesKeys.filter((k) => !locInfoKeys.includes(k));
