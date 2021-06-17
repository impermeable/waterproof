/* eslint-disable no-unused-vars */
const {toAST, astHasChild, keyify} = require('./helpers/CoqASTHelpers');

const chai = require('chai');
const {emptyAst, empty, sexp1, sexpRequire, sexpHint, Ltac2NB} =
  require('./helpers/SExprList');
// eslint-disable-next-line @typescript-eslint/no-unused-vars
const expect = chai.expect;

describe('Parsing CoqASTs', () => {
  it('should parse an empty Coq AST s-expr correctly', (done) => {
    const ast = toAST(emptyAst);

    expect(ast.constructor.name).to.equal('CoqAST');
    expect(ast.content).to.eql([]);
    expect(ast.locinfo.line_nb).to.equal(1);

    done();
  });

  it('shoud produce empty AST for empty S-Expr', (done) => {
    const ast = toAST(empty);
    expect(ast).to.equal(null);
    done();
  });

  it('should parse simple S-Expr', (done) => {
    const ast = toAST(sexp1);
    // expect(ast.constructor.name).to.equal('CoqAST');
    // astHasChild(ast, '');
    ['LocInfo', 'VernacStartTheoremProof', 'CLocalAssum']
        .forEach(
            (child) => expect(astHasChild(ast, child)).to.be.true);
    expect(astHasChild(ast, 'Object')).not.to.be.true;
    expect(astHasChild(ast, 'DefineBody')).not.to.be.true;
    done();
  });

  it('should parse Require Import sexpr', (done) => {
    const ast = toAST(sexpRequire);

    expect(ast.constructor.name).to.equal('CoqAST');
    expect(astHasChild(ast, 'VernacRequire')).to.be.true;
    expect(astHasChild(ast, '.VernacRequire.SerQualid')).to.be.true;
    expect(ast.content.data.list[0].content.id).to.eql('Reals');
    console.log(keyify(ast));
    done();
  });

  it('should parse Hint Sexpr', (done) => {
    const ast = toAST(sexpHint);

    expect(astHasChild(ast, 'VernacHints.HintsResolve.HintsReference'))
        .to.be.true;
    expect(astHasChild(ast, 'HintsReference.SerQualid'))
        .to.be.true;
    done();
  });

  it('should parse a complete Ltac proof', (done) => {
    let lineNb = 1;
    Ltac2NB.split('\n').forEach((sentence) => {
      const ast = toAST(sentence);
      expect(ast.constructor.name).to.equal('CoqAST');
      lineNb++;
      // expect(ast.locinfo.line_nb).to.equal(lineNb++);
    });
    expect(lineNb).to.equal(14);
    done();
  });
});
