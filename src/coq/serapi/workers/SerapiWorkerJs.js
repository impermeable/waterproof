'use strict';

import SerapiWorker from './SerapiWorker';

/**
 * Class that connects to serapi
 */
class SerapiWorkerJs extends SerapiWorker {
  /**
   * Interface (non implementation) of SerapiWorker
   * @param {String} workerLocation
   */
  constructor(workerLocation='../../jscoq-builds/sertop_js.js') {
    super();
    this.worker = new Worker(workerLocation);
    this.worker.onmessage = (m) => this.handleMessage(m);
    this.worker.onerror =(error) => {
      console.log('js worker error:');
      console.log(error);
    };
  }

  /**
   * Send message
   * @param {String} message the message
   */
  postMessage(message) {
    this.worker.postMessage(message);
  }

  /**
   * Receives the messages from the worker
   * @param {String} message the message
   */
  handleMessage(message) {
    this.onMessage(message.data);
  }

  /**
   * Stop this worker
   */
  terminate() {
    this.worker.terminate();
  }
}

export default SerapiWorkerJs;
