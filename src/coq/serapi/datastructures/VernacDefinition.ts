/* eslint-disable no-unused-vars */
/* eslint-disable require-jsdoc */
import {convertToASTComp} from '../ASTProcessor';
import CoqType from './CoqType';
import LocInfo from './LocInfo';

enum DefinitionObjectKind {
  Definition= 'Definition',
  Coercion = 'Coercion',
  SubClass = 'SubClass',
  CanonicalStructure = 'CanonicalStructure',
  Example = 'Example',
  Fixpoint = 'Fixpoint',
  CoFixpoint = 'CoFixpoint',
  Scheme = 'Scheme',
  StructureComponent = 'StructureComponent',
  IdentityCoercion = 'IdentityCoercion',
  Instance = 'Instance',
  Method = 'Method',
  Let = 'Let',
}

export default class VernacDefinition extends CoqType {
  discharge: boolean;
  defintionObjectKind: DefinitionObjectKind;
  nameDecl: { name: { locinfo: LocInfo; content: any; }; options: any; };
  defitionExpr: any;
  constructor( array ) {
    super();

    this.discharge = array[1][0] === 'DoDischarge';
    this.defintionObjectKind = array[1][1];

    this.nameDecl = {
      name: {
        locinfo: new LocInfo(['loc', array[2][0].loc]),
        content: convertToASTComp(array[2][0].v),
      },
      options: array[2][1],
    };

    // ProofBody | DefineBody
    this.defitionExpr = convertToASTComp(array[3]);
  }

  pprint(): string {
    throw new Error('Method not implemented.');
  }
}
