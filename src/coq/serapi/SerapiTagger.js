import parse from 's-expression';
import * as Constants from './SerapiConstants';
import {parseErrorableFeedback} from './SerapiParser';

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
    this.lastCallbacks = {
      handleMessage: () => readyCallback,
      handleFeedback: () => {},
    };
    this.commandStartTime = null;

    this.timing = false;
  }

  _getTag() {
    const tag = 'wp' + this.currentTag;
    this.currentTag++;
    return tag;
  }

  _resetCurrentMessage() {
    this.lastTag = null;
    this.lastCallbacks = null;
    this.commandStartTime = null;
  }

  /**
   *
   * @param {String} command
   * @param {Function} messageHandler
   * @param {Function} feedbackHandler
   * @param {String} extraTag
   */
  sendCommand(command, messageHandler, feedbackHandler, extraTag) {
    this.lastTag = extraTag == null ? this._getTag() :
        this._getTag() + '-' + extraTag;
    this.lastCallbacks = {
      handleMessage: messageHandler,
      handleFeedback: feedbackHandler,
    };
    const serapiCommand = `(${this.lastTag} ${command})`;
    console.log(`Serapi <- ${serapiCommand}`);
    this.worker.postMessage(serapiCommand);
  }

  handleMessage(message) {
    console.log(`Serapi -> ${message}`);
    if (!this.lastCallbacks) {
      // no callback ignore
      console.error('Got message while no callback registered');
      console.log(message);
      return;
    }

    const data = message.replace(/ ,\)/g, ' ",")')
        .replace(/'\)/g, ' "\'")');
    const parsedData = parse(data);

    if (parsedData[0] !== 'Feedback') {
      const tag = parsedData[1];
      if (tag !== this.lastTag) {
        console.log('Received message with non current tag');
      } else if (this.timing && parsedData[2] === Constants.MESSAGE_ACK) {
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

      if (parsedData[2] === Constants.MESSAGE_COMPLETED) {
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
        this.lastCallbacks.handleFeedback(feedback);
      }
    }
  }
}

export default SerapiTagger;
