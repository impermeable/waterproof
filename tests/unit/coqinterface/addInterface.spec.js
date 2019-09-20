import CoqSerapi from '../../../src/coq/serapi/CoqSerapi';
import SerapiInterface from '../../../src/coq/serapi/SerapiInterface';
import EditorInterface from '../../../src/coq/EditorInterface';

const sinon = require('sinon');
const chai = require('chai');
const sandbox = sinon.createSandbox();
const expect = chai.expect;

describe('setContent', () => {
  // Replace all the functions of the interface with SerAPI by fakes
  // See https://sinonjs.org/releases/v7.3.2/fakes/
  const serapi = new SerapiInterface;
  const callbacks = new EditorInterface;

  const oneDot = '.';
  const twoDots = '..';

  serapi.add = function(text, onSuccess) {
    onSuccess([{beginIndex: 0, endIndex: text.trim().length, sentenceId: 0}]);
  };

  serapi.cancel = function(sentence, onSuccess) {
    onSuccess(sentence);
  };

  let setContentDone = false;

  callbacks.setContentError = function() {
    setContentDone = true;
  };

  callbacks.setContentSuccess = function() {
    setContentDone = true;
  };

  let impl;
  let addSpy;
  let cancelSpy;
  let errorSpy;

  beforeEach(() => {
    // Before each test, reset the call counts etc. of all the fake functions

    addSpy = sinon.spy(serapi, 'add');
    cancelSpy = sinon.spy(serapi, 'cancel');
    errorSpy = sinon.spy(callbacks, 'setContentError');

    impl = new CoqSerapi(serapi, callbacks);
  });

  afterEach(() => {
    sinon.restore();
    sandbox.restore();
  });

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

  it('should reject code that does not end in a "."', (done) => {
    // Send setContent a string that does not end in a "."
    // Then, we expect the onError function to be called
    const text = 'Lemma a1: forall n: nat, n + 0 = n. Proof';
    setContent(text).then(() => {
      expect(errorSpy.callCount).to.equal(1);
      done();
    });

    // Note: the responses to onSuccess and onError are usually asynchronous,
    // so we cannot test them properly here
  });

  it('should call the "add" method if the content changed', (done) => {
    const text = 'Lemma a2; forall n: nat, n + 0 = n. Proof.';
    setContent(text).then(() => {
      expect(serapi.add.callCount).to.be.equal(1);
      expect(serapi.add.lastCall.args[0]).to.be.equal(text);
      done();
    });
  });

  it('should not call the "add" method if the content did not change',
      (done) => {
        const text = 'Lemma a3: forall n: nat, n + 0 = n. Proof.';
        setContent(text).then(() => {
          expect(addSpy.callCount).to.be.equal(1);
          expect(addSpy.lastCall.args[0]).to.be.equal(text);
          setContent(text).then(() => {
            expect(addSpy.callCount).to.be.equal(1);
            done();
          });
        });
      });

  it('should not call "add" on entire content if only a string is appended',
      (done) => {
        // Call setContent twice, the second time with one extra sentence
        // The callbacks are not important, because no response is ever given
        const textPart1 = 'Lemma a4: forall n: nat, n + 0 = n. ';
        const textPart2 = 'Proof.';
        setContent(textPart1)
            .then(() => impl.setContent(textPart1 + textPart2)
                .then(() => {
                  // We should see two calls, the second one with only "Proof."
                  // We call trim() on all the compared strings to prevent
                  // errors due to slightly different handling of spaces between
                  // sentences
                  expect(addSpy.callCount).to.be.equal(2);
                  expect(addSpy.getCall(0).args[0].trim()).to.be
                      .equal(textPart1.trim());
                  expect(addSpy.lastCall.args[0].trim()).to
                      .equal(textPart2.trim());
                  done();
                }));
      });

  it('should call "add" on last sentence if two periods are appended',
      (done) => {
        // Call setContent twice, the second time with two extra periods
        const text = 'Lemma a5: forall n: nat, n + 0 = n.';
        setContent(text)
            .then(() => {
              expect(addSpy.callCount).to.be.equal(1);
              expect(addSpy.getCall(0).args[0]).to.equal(text);
              setContent(text + twoDots)
                  .then(() => {
                    // We should see two calls, the second should contain the
                    // whole sentence again.
                    expect(addSpy.callCount).to.be.equal(2);
                    expect(addSpy.getCall(1).args[0]).to.equal(text + twoDots);
                    done();
                  });
            });
      }
  );

  it('should call "add" on last sentence if one period is appended twice',
      (done) => {
        // Call setContent three times, the second time with one extra period,
        // the third with two extra periods
        const text = 'Lemma a6: forall n: nat, n + 0 = n.';
        setContent(text)
            .then(() => {
              expect(addSpy.callCount).to.be.equal(1);
              expect(addSpy.getCall(0).args[0]).to.equal(text);
              setContent(text + oneDot)
                  .then(() => {
                    expect(addSpy.callCount).to.be.equal(2);
                    expect(addSpy.getCall(1).args[0]).to.equal(text + oneDot);
                    setContent(text + twoDots)
                        .then(() => {
                          // We should see two calls, the second should contain
                          // the whole sentence again.
                          expect(addSpy.callCount).to.be.equal(3);
                          expect(addSpy.getCall(2).args[0]).to
                              .equal(text + twoDots);
                          done();
                        });
                  });
            });
      }
  );

  it('should call "add" after removing two periods from sentence with three',
      (done) => {
        // Call setContent two times, the second time with two fewer periods
        const text = 'Lemma a7: forall n: nat, n + 0 = n.';
        setContent(text + twoDots)
            .then(() => {
              expect(addSpy.callCount).to.be.equal(1);
              expect(addSpy.getCall(0).args[0]).to.equal(text + twoDots);
              setContent(text)
                  .then(() => {
                    expect(addSpy.callCount).to.be.equal(2);
                    expect(addSpy.getCall(1).args[0]).to.equal(text);
                    done();
                  });
            });
      }
  );

  it('should call "add" after twice removing a period from sentence with three',
      (done) => {
        // Call setContent three times, the second time with one fewer period,
        // the third with two fewer periods
        const text = 'Lemma a8: forall n: nat, n + 0 = n.';
        setContent(text + twoDots)
            .then(() => {
              expect(addSpy.callCount).to.be.equal(1);
              expect(addSpy.getCall(0).args[0]).to.equal(text + twoDots);
              setContent(text + oneDot)
                  .then(() => {
                    expect(addSpy.callCount).to.be.equal(2);
                    expect(addSpy.getCall(1).args[0]).to.equal(text + oneDot);
                    setContent(text)
                        .then(() => {
                          expect(addSpy.callCount).to.be.equal(3);
                          expect(addSpy.getCall(2).args[0]).to
                              .equal(text);
                          done();
                        });
                  });
            });
      }
  );


  it('should wipe content when setContent("") is called', (done) => {
    const text = 'Lemma a9: forall n: nat, n + 0 = n. Proof.';
    setContent(text)
        .then(() => setContent('')
            .then(() => {
            // We should see at least 1 call to cancel(), none to onError and
            // currentContent is set to empty string
              expect(cancelSpy.callCount).to.be.at.least(1);
              expect(errorSpy.callCount).to.equal(0);
              expect(impl.currentContent).to.equal('');
              done();
            })
        );
  });

  it('should cancel a sentence when it is removed from the end of content',
      (done) => {
        const textPart1 = 'Lemma a10: forall n: nat, n + 0 = n. ';
        const textPart2 = 'Proof.';
        setContent(textPart1 + textPart2)
            .then(() => setContent(textPart1)
                .then(() => {
                // We should see 1 call to cancel(), none to onError and
                // previousCall is updated accordingly
                  expect(cancelSpy.callCount).to.equal(1);
                  expect(errorSpy.callCount).to.equal(0);
                  expect(impl.currentContent).to.be.equal(textPart1);
                  done();
                })
            );
      }
  );

  it('should cancel a sentence when it is removed from the middle of content',
      (done) => {
        const textPart1 = 'Lemma a11: forall n: nat, n + 0 = n. ';
        const textPart2 = 'Proof.';
        const textPart3 = 'intros n.';
        setContent(textPart1 + textPart2 + textPart3)
            .then(() => setContent(textPart1 + textPart3)
                .then(() => {
                  // We should see 1 call to cancel(), none to onError and
                  // previousCall is updated accordingly
                  expect(cancelSpy.callCount).to.equal(1);
                  expect(errorSpy.callCount).to.equal(0);
                  expect(impl.currentContent).to.be
                      .equal(textPart1 + textPart3);
                  done();
                })
            );
      }
  );

  it('should cancel sentences when they are removed from the content',
      (done) => {
        const textPart1 = 'Lemma a12: forall n: nat, n + 0 = n. ';
        const textPart2 = 'Proof.';
        const textPart3 = 'intros n.';
        const textPart4 = 'auto.';
        const textPart5 = 'Qed.';
        setContent(textPart1 + textPart2 + textPart3 + textPart4 +
          textPart5)
            .then(() => setContent(textPart1 + textPart3 + textPart5)
                .then(() => {
                  // We should see 1 call to cancel(), none to onError and
                  // previousCall is updated accordingly
                  expect(cancelSpy.callCount).to.equal(1);
                  expect(errorSpy.callCount).to.equal(0);
                  expect(impl.currentContent).to.be
                      .equal(textPart1 + textPart3 + textPart5);
                  done();
                })
            );
      });

  it('should rollback execution when the content is changed',
      (done) => {
        serapi.add = function(text, onSuccess) {
          onSuccess([
            {beginIndex: 0, endIndex: 20, sentenceId: 0},
            {beginIndex: 21, endIndex: 27, sentenceId: 1},
            {beginIndex: 28, endIndex: 44, sentenceId: 2},
            {beginIndex: 45, endIndex: 49, sentenceId: 3},
          ]);
        };

        const textVersion1 =
            'Lemma a9 n: n+0 = n. Proof. now induction n. Qed.';
        const textVersion2 =
            'Lemma a9 n: n+0 = n. Proof.\nnow induction n. Qed.';
        impl.setContent(textVersion1)
            .then(() => {
              impl.lastExecuted = 4;
              impl.getGoalsAtSentence = function(sentence, onSuccess) {
                expect(sentence).to.equal(1);
                onSuccess('n+0 = n');
              };
              const getGoalsSpy = sinon.spy(impl, 'getGoalsAtSentence');

              setContent(textVersion2)
                  .then(() => {
                    expect(impl.lastExecuted).to.equal(1);
                    expect(getGoalsSpy.callCount).to.equal(1);
                    expect(errorSpy.callCount).to.equal(0);
                    done();
                  });
            });
      }
  );
});
