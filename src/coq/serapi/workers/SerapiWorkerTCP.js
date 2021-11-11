'use strict';

import SerapiWorker from './SerapiWorker';

/**
 * Class that connects to serapi
 */
class SerapiWorkerTCP extends SerapiWorker {
  /**
   * Interface (non implementation) of SerapiWorker
   * @param {TCPManager} socket the manager to send messages with
   * @param {string} sertopPath the path where to find sertop
   */
  constructor(socket, sertopPath='') {
    super();
    this.socket = socket;
    this.socketId = -1;

    this.sendMessage(
        this.createWrapperMessage('create',
            JSON.stringify({path: sertopPath,
              args: ['--implicit',
                // `--load-path=${wplibPath},wplib`,
                // TODO: Either remove the compilation part completely
                //       or make sure the wplib folder exists.
              ]}))
    );
  }

  /**
   * Create a message for the wrapper
   * Auto injects the id
   * @param {String} command the command/verb
   * @param {String} content the content of the command/verb
   * @return {string|{instance_id: number, verb: *, content: string}}
   */
  createWrapperMessage(command, content='') {
    if (command !== 'create' && this.socketId < 0) {
      console.warn('Message sent too soon');
    }
    return {
      verb: command,
      instance_id: this.socketId,
      content: content,
    };
  }

  /**
   * Send message
   * @param {String} message the message
   */
  postMessage(message) {
    this.sendMessage(
        this.createWrapperMessage('forward', message)
    );
  }

  /**
   * Send a real wrapper message
   * @param {String} wrapperMessage the wrapper message to send
   */
  sendMessage(wrapperMessage) {
    this.socket.sendMessage(JSON.stringify(wrapperMessage));
  }

  /**
   * Handle a message from the socket
   * @param {String} message the message
   */
  handleMessage(message) {
    if (message !== '') {
      this.onMessage(message);
    }
  }

  /**
   * Stop this worker
   */
  terminate() {
    this.sendMessage(
        this.createWrapperMessage('destroy')
    );
  }
}

export default SerapiWorkerTCP;
