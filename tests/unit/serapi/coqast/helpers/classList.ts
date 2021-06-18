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
import InConstrEntry from
  '../../../../../src/coq/serapi/datastructures/InConstrEntry';
import SerQualid from '../../../../../src/coq/serapi/datastructures/SerQualid';
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
  'VernacExpr': {
    class: VernacExpr,
    goodIn: ['VernacExpr', '', empty],
    badIn: [],
  },
  'VernacExtend': {
    class: VernacExtend,
    goodIn: [],
    badIn: [],
  },
  'v': {
    class: GenericVType,
    goodIn: ['v', [['attrs', 1], ['control', ''], ['expr', empty]]],
    badIn: [],
  },
  'VernacRequire': {
    class: VernacRequire,
    goodIn: ['VernacRequire', '121', 'false', []],
    badIn: [],
  },
  'Ser_Qualid': {
    class: SerQualid,
    goodIn: ['Ser_Qualid', ['', ''], ['', 12]],
    badIn: [],
  },
  'VernacStartTheoremProof': {
    class: VernacStartTheoremProof,
    goodIn: ['VernacStartTheoremProof', 'Lemma', [[]]],
    badIn: [],
  },
  'VernacProof': {
    class: VernacProof,
    goodIn: [],
    badIn: [],
  },
  'VernacEndProof': {
    class: VernacEndProof,
    goodIn: ['Proved', ''],
    badIn: [],
  },
  'CNotation': {
    class: CNotation,
    goodIn: ['CNotation', '', empty, [[], [], [], []]],
    badIn: [],
  },
  'InConstrEntry': {
    class: InConstrEntry,
    goodIn: [],
    badIn: [],
  },
  'CRef': {
    class: CRef,
    goodIn: ['CRef', {loc: baseLoc, v: empty}, {}],
    badIn: [],
  },
  'CPrim': {
    class: CPrim,
    goodIn: ['CPrim', ['Non-Numeric', []]],
    badIn: [],
  },
  'CProdN': {
    class: CProdN,
    goodIn: ['CProdN', [], {loc: baseLoc, v: empty}],
    badIn: [],
  },
  'CApp': {
    class: CApp,
    goodIn: ['CApp', ['', {loc: baseLoc, v: empty}], []],
    badIn: [],
  },
  'CLocalAssum': {
    class: CLocalAssum,
    goodIn: ['CLocalAssum', [], [], {loc: baseLoc, v: empty}],
    badIn: [],
  },
  'VernacDefinition': {
    class: VernacDefinition,
    goodIn: ['VernacDefinition', ['DoDischarge', ''], [{loc: baseLoc, v: empty},
      []], empty],
    badIn: [],
  },
  'DefineBody': {
    class: DefineBody,
    goodIn: ['DefineBody', [], [], {loc: baseLoc, v: empty}, []],
    badIn: [],
  },
  'CLambdaN': {
    class: CLambdaN,
    goodIn: ['CLambdaN', [], {loc: baseLoc, v: empty}],
    badIn: [],
  },
  'VernacHints': {
    class: VernacHints,
    goodIn: ['VernacHints', '', empty],
    badIn: [],
  },
  'HintsResolve': {
    class: HintsResolve,
    goodIn: ['HintsResolve', []],
    badIn: [],
  },
  'HintsReference': {
    class: HintsReference,
    goodIn: ['HintsReference', {loc: baseLoc, v: empty}],
    badIn: [],
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
    data: ['CProdN', [], {loc: baseLoc, v: empty}],
  },
  'CRef': {
    class: CRef,
    data: ['CRef', {loc: baseLoc, v: empty}, {}],
  },
  'HintsReference': {
    class: HintsReference,
    data: ['HintsReference', {loc: baseLoc, v: ['VernacExtend', '', '']}],
  },
  // 'VernacDefinition': {
  //   class: VernacDefinition,
  // eslint-disable-next-line max-len
  //   data: ['VernacDefinition', ['DoDischarge', ''], [{loc: baseLoc, v: empty},
  //     []], empty],
  // },
  'DefineBody': {
    class: DefineBody,
    data: ['DefineBody', [], [], {loc: baseLoc, v: empty}, []],
  },
};
