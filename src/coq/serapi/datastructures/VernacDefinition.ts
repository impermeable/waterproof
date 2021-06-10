/* eslint-disable no-unused-vars */
/* eslint-disable require-jsdoc */
import {convertToASTComp} from '../ASTProcessor';
import CoqType, {Visitable} from './CoqType';
import LocInfo from './LocInfo';
import ASTVisitor from './visitor/ASTVisitor';

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

class VernacDefinition extends CoqType implements Visitable {
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

  pprint(indent = 0): string {
    const tab = '\n'.concat('\t'.repeat(indent+1));
    let output = '';
    output = output.concat('Discharge: ', this.discharge.toString(), tab);
    output = output.concat('Def: ', this.defintionObjectKind.toString(), tab);
    output = output.concat('Name: ', tab);
    output = output.concat('\tLoc: ',
        this.nameDecl.name.locinfo.pprint(indent+1), tab);
    output = output.concat('\t', this.cprint(this.nameDecl.name.content,
        indent+1));
    return this.sprintf(super.pprint(indent), output);
    // throw new Error('Method not implemented.');
  }

  accept(visitor: ASTVisitor) {
    visitor.visitVernacDefinition(this);
    // visitor.visitCNotation(this.);
  }
}

export default VernacDefinition;
