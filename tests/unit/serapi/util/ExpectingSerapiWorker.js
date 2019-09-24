/* eslint-disable require-jsdoc */
import SerapiWorker from '../../../../src/coq/serapi/workers/SerapiWorker';

const chai = require('chai');
const expect = chai.expect;

class ExpectingSerapiWorker extends SerapiWorker {
  constructor() {
    super();
    this.expectedIndex = 0;
    this.expectedCalls = [];
    this.calls = [];
  }

  addExpectedCall(command, responses, callback=null) {
    this.expectedCalls.push({
      command,
      responses,
      callback,
    });
  }

  async postMessage(message) {
    this.calls.push(message);

    if (this.expectedCalls.length > this.expectedIndex) {
      // if we have an expected call check and return the response
      const tag = message.split('(')[1];
      const currentCall = this.expectedCalls[this.expectedIndex];
      this.expectedIndex++;

      expect(message).to.include(currentCall.command);

      // first callback then any possible messages
      if (currentCall.callback) {
        await currentCall.callback(message);
      }

      for (const partialResult of currentCall.responses) {
        if (partialResult.startsWith('(Feedback')
          || partialResult.startsWith('(Answer')) {
          this.onMessage(partialResult);
        } else {
          if (!partialResult.startsWith('(')) {
            this.onMessage(`(Answer ${tag} ${partialResult})`);
          } else {
            // no space between
            this.onMessage(`(Answer ${tag}${partialResult})`);
          }
        }
      }
    } else {
      console.log('Not expecting any message!');
      expect(true).to.equal(false);
    }
  }

  getCallAmount() {
    return this.calls.length;
  }

  getCall(n) {
    return this.calls[n];
  }

  hasCall(condition) {
    return this.calls.some(condition);
  }

  sendMessages(messages) {
    for (const message of messages) {
      this.onMessage(message);
    }
  }
}

export default ExpectingSerapiWorker;
