import CoqSerapi from '../../../src/coq/serapi/CoqSerapi';
import SerapiInterface from '../../../src/coq/serapi/SerapiInterface';
import EditorInterface from '../../../src/coq/EditorInterface';

const sinon = require('sinon');
const chai = require('chai');
const sandbox = sinon.createSandbox();
const expect = chai.expect;
const text = 'Lemma a0: forall n: nat, n + 0 = n. Proof.';

describe('execute interface', () => {
  // Replace all the functions of the interface with SerAPI by fakes
  // See https://sinonjs.org/releases/v7.3.2/fakes/
  const serapi = new SerapiInterface;
  const callbacks = new EditorInterface;

  serapi.exec = function(id, onSuccess) {
    onSuccess();
  };

  serapi.goals = function(id, onSuccess) {
    onSuccess('fake goal');
  };

  let impl;

  let setContentDone = false;
  let executeDone = false;

  callbacks.setContentError = function() {
    setContentDone = true;
  };

  callbacks.setContentSuccess = function() {
    setContentDone = true;
  };

  callbacks.executeSuccess = function() {
    executeDone = true;
  };

  callbacks.executeError = function() {
    executeDone = true;
  };

  const setContent = async function(text) {
    return new Promise(async (resolve) => {
      setContentDone = false;
      impl.setContent(text);

      while (!setContentDone) {
        await new Promise((resolve) => setTimeout(resolve, 2));
      }
      setContentDone = false;
      resolve();
    });
  };

  let goalSpy;
  let execSpy;
  let startedSpy;
  let errorSpy;

  // Before each test, reset the call counts etc. of all the fake functions
  beforeEach(async () => {
    executeDone = false;
    setContentDone = false;
    sandbox.replace(serapi, 'add', (code, onSuccess, ignored) => {
      onSuccess([
        {sentenceId: 2, beginIndex: 0, endIndex: 35},
        {sentenceId: 3, beginIndex: 36, endIndex: 42}]
      );
    });
    sandbox.replace(serapi, 'cancel', sinon.fake());

    execSpy = sinon.spy(serapi, 'exec');
    goalSpy = sinon.spy(serapi, 'goals');
    startedSpy = sinon.spy(callbacks, 'executeStarted');
    errorSpy = sinon.spy(callbacks, 'executeError');

    impl = new CoqSerapi(serapi, callbacks);

    await setContent(text);
  });

  afterEach(() => {
    sinon.restore();
    sandbox.restore();
  });

  const executionDone = () => {
    return new Promise(async (resolve) => {
      while (!executeDone) {
        await new Promise((resolve) => setTimeout(resolve, 2));
      }

      executeDone = false;
      resolve();
    });
  };

  const executeNext = () => {
    return impl.executeNext()
        .then(() => executionDone());
  };

  const executePrevious = () => {
    return impl.executePrevious()
        .then(() => executionDone());
  };

  const executeTo = (to) => {
    return impl.executeTo(to)
        .then(() => executionDone());
  };


  describe('executeNext', () => {
    it('should execute next if nothing has been executed', (done) => {
      executeNext()
          .then(() => {
            expect(startedSpy.callCount).to.equal(1);
            expect(errorSpy.callCount).to.equal(0);
            expect(impl.lastExecuted).to.equal(0);
            expect(execSpy.callCount).to.equal(1);
            done();
          });
    });


    it('should execute last line', (done) => {
      executeNext()
          .then(() => executeNext())
          .then(() => {
            expect(startedSpy.callCount).to.equal(2);
            expect(errorSpy.callCount).to.equal(0);
            expect(impl.lastExecuted).to.equal(1);
            expect(execSpy.callCount).to.equal(2);
            done();
          });
    });

    it('should not throw error when executing line after the last', (done) => {
      executeNext()
          .then(() => executeNext())
          .then(() => executeNext())
          .then(() => {
            expect(impl.lastExecuted).to.equal(1);
            expect(startedSpy.callCount).to.equal(2);
            expect(errorSpy.callCount).to.equal(1);
            done();
          });
    });

    it('should set last executed to -1 if execute next is followed by previous',
        (done) => {
          executeNext()
              .then(() => executePrevious())
              .then(() => {
                expect(impl.lastExecuted).to.equal(-1);
                done();
              });
        });
  });

  describe('executePrevious', () => {
    it('should not executePrevious if on the first line', (done) => {
      executePrevious()
          .then(() => {
            expect(startedSpy.callCount).to.equal(0);
            expect(errorSpy.callCount).to.equal(1);
            done();
          });
    });


    it('should execute next and then previous', (done) => {
      executeNext()
          .then(() => executePrevious())
          .then(() => {
            expect(startedSpy.callCount).to.equal(2);
            expect(errorSpy.callCount).to.equal(0);
            done();
          });
    });
  });

  describe('executeTo', () => {
    it('should execute the current line if cursor is on last character',
        (done) => {
          executeTo(35)
              .then(() => {
                expect(impl.lastExecuted).to.equal(0);
                expect(execSpy.callCount).to.equal(1);
                done();
              });
        });


    it('should execute everything if cursor is on last line last character',
        (done) => {
          executeTo(42)
              .then(() => {
                expect(impl.lastExecuted).to.equal(1);
                expect(execSpy.callCount).to.equal(2);
                done();
              });
        });


    it('should not execute any sentence when cursor is on the first line',
        (done) => {
          executeTo(6)
              .then(() => {
                expect(errorSpy.callCount).to.equal(0);
                expect(execSpy.callCount).to.equal(0);
                done();
              });
        });


    it('should execute sentences before chosen', (done) => {
      executeTo(40)
          .then(() => {
            expect(errorSpy.callCount).to.equal(0);
            expect(impl.lastExecuted).to.equal(0);
            expect(execSpy.callCount).to.equal(1);
            done();
          });
    });


    it('for already executed sentences only the goals should be given',
        (done) => {
          executeTo(42).then( () => {
            const execCount = execSpy.callCount;
            expect(goalSpy.callCount).to.equal(1);
            executeTo(38).then( () => {
              expect(errorSpy.callCount).to.equal(0);
              expect(execSpy.callCount).to.equal(execCount);
              expect(goalSpy.callCount).to.equal(2);
              done();
            });
          });
        });


    it('should not display goals or execute when going to the first line',
        (done) => {
          executeTo(42).then( () => {
            const execCount = execSpy.callCount;

            executeTo(7).then( () => {
              expect(errorSpy.callCount).to.equal(0);
              expect(execSpy.callCount).to.equal(execCount);
              expect(goalSpy.callCount).to.equal(1);
              done();
            });
          });
        });


    it('should not execute code that is not added', (done) => {
      executeTo(text.length + 1)
          .then(() => {
            expect(0).to.be.equal(1);
          })
          .catch(() => {
            done();
          });
    });


    it('should reject executing with negative index', (done) => {
      executeTo(-1)
          .then(() => {
            expect(0).to.be.equal(1);
          })
          .catch(() => {
            done();
          });
    });
  });
});
