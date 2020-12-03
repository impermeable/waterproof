import parse from 's-expression';
import {
  isReadyFeedback,
  MESSAGE_ACK,
  MESSAGE_COMPLETED,
  parseErrorableFeedback,
} from './SerapiParser';

/**
 * A class that wraps promises around messages send to Serapi
 * It also keep track of tags to allow differentiation of messages
 */
class SerapiTagger {
  /**
   *
   * @param {SerapiWorker} worker
   * @param {Function} readyCallback
   */
  constructor(worker, readyCallback) {
    // TODO: maybe merge into worker?
    this.worker = worker;
    this.worker.onMessage = (m) => this.handleMessage(m);
    this.currentTag = 0;

    this.lastTag = null;
    this.lastCallbacks = readyCallback ? {
      handleMessage: () => {
      },
      handleFeedback: (message, raw) => {
        if (raw && isReadyFeedback(message)) {
          readyCallback();
          this._resetCurrentMessage();
        }
      },
    } : null;
    this.commandStartTime = null;

    this.timing = false;
    this.logging = false;
  }

  /**
   * Get the tag for the next message
   * @return {string} the tag for the next message
   * @private
   */
  _getTag() {
    const tag = 'wp' + this.currentTag;
    this.currentTag++;
    return tag;
  }

  /**
   * Reset and get ready for new message
   * @private
   */
  _resetCurrentMessage() {
    this.lastTag = null;
    this.lastCallbacks = null;
    this.commandStartTime = null;
  }

  /**
   * Send a command to serapi with a unique tag
   * @param {String} command The command to send
   * @param {Function} messageHandler the message handler
   * @param {Function} feedbackHandler the feedback handler
   * @param {String} extraTag the extra identifying tag
   */
  sendCommand(command, messageHandler, feedbackHandler, extraTag) {
    if (this.lastCallbacks != null) {
      console.log('overwriting message while previous not finished!');
    }
    this.lastTag = extraTag == null ? this._getTag() :
        this._getTag() + '-' + extraTag;
    this.lastCallbacks = {
      handleMessage: messageHandler,
      handleFeedback: feedbackHandler,
    };
    const serapiCommand = `(${this.lastTag} ${command})`;
    if (this.logging) {
      console.log(`Serapi <- ${serapiCommand}`);
    }
    this.worker.postMessage(serapiCommand);
  }

  /**
   * Hanlde a message from the worker
   * @param {String} message the serapi message (generic can be feedback)
   */
  handleMessage(message) {
    if (this.logging) {
      console.log(`Serapi -> ${message}`);
    }
    if (!this.lastCallbacks) {
      // no callback ignore
      console.error('Got message while no callback registered');
      console.log(message);
      return;
    }

    const data = message.replace(/,\)/g, ' ",")');
    const parsedData = parse(data);
    if (parsedData instanceof Error) {
      console.log('Could not parse: ', data);
      console.warn(parsedData);
      alert('Could not parse message: ' + message);
      return;
    }

    if (parsedData[0] !== 'Feedback') {
      const tag = parsedData[1];
      if (tag !== this.lastTag) {
        console.log('Received message with non current tag', this.lastTag);
        console.log(parsedData);
      } else if (this.timing && parsedData[2] === MESSAGE_ACK) {
        this.commandStartTime = +new Date();
      }

      let extraTag = null;
      if (parsedData.length > 1) {
        const tag = parsedData[1].split('-', 2);
        if (tag.length > 1) {
          extraTag = tag[1];
        }
      }

      this.lastCallbacks.handleMessage(parsedData[2], extraTag);

      if (parsedData[2] === MESSAGE_COMPLETED) {
        if (this.timing && this.commandStartTime != null) {
          const time = Math.round(
              (+new Date()) - this.commandStartTime) / 1000;
          console.log(`${tag} took ${time}s`);
        }
        this._resetCurrentMessage();
      }
    } else {
      // feedback is not tagged but should be from the current command
      const feedback = parseErrorableFeedback(parsedData);
      if (feedback.string !== '') {
        this.lastCallbacks.handleFeedback(feedback, false);
      } else {
        this.lastCallbacks.handleFeedback(parsedData, true);
      }
    }
  }
}

export default SerapiTagger;
