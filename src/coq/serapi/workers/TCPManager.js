import SerapiWorkerTCP from './SerapiWorkerTCP';
import {Mutex} from 'async-mutex/lib/index';

const ipc = require('node-ipc');

const INT_SIZE = 4;
const ENCODING = 'utf8';

/**
 * A class that persists the connection to the wrapper
 * And handles dealing out socket ids
 */
class TCPManager {
  /**
   *
   * @param {Integer} port the port of the TCP socket
   * @param {Boolean} createSocket create the socket immediately
   */
  constructor(port=-1, createSocket=true) {
    this.port = port;
    this.socketId = 'waterproof-wrapper';
    this.serapis = [];
    this.disconnecting = null;

    this.charLeftToRead = -1;
    this.bufferSoFar = null;
    this.writeLock = new Mutex;

    this.partialBuffer = null;

    if (createSocket) {
      this.ready = false;
      this.readyWaiters = [];
      this.setupConnection()
          .then((port) => {
            this.port = port;
            this.ready = true;
            this.readyWaiters.forEach((fn) => fn());
            this.readyWaiters.length = 0;
          });
    } else {
      this.ready = true;
    }
  }

  /**
   * Start the connection to the socket
   */
  async setupConnection() {
    if (ipc.of[this.socketId] !== undefined) {
      ipc.of[this.socketId].on(
          'data',
          (data) => this.handleBuffer(data)
      );
      // socket already started
      return;
    }

    ipc.config.stopRetrying = 0;
    ipc.config.maxRetries = 0;
    ipc.config.rawBuffer = true;
    ipc.config.silent = true;
    ipc.config.encoding = 'hex';

    /* eslint-disable no-console */
    const oldError = console.error;
    console.error = () => {};

    const {ipcRenderer} = require('electron');

    const port = await ipcRenderer.invoke('serapi-port');

    ipc.connectToNet(this.socketId,
        port,
        () => {
          ipc.of[this.socketId].on(
              'data',
              (data) => this.handleBuffer(data)
          );
        });

    setTimeout(() => {
      if (console.error == null) {
        console.error = oldError;
      }
    }, 0);
    /* eslint-enable no-console */

    return port;
  }

  /**
   * Check if we can create workers already
   */
  async readyForConnections() {
    if (this.ready) {
      return;
    }

    return new Promise((resolve) => {
      this.readyWaiters.push(resolve);
    });
  }

  /**
   * Create a new worker
   * @param {string} sertopPath The path of sertop
   * @return {SerapiWorkerTCP} the worker
   */
  async createNewWorker(sertopPath='') {
    await this.readyForConnections();
    const worker = new SerapiWorkerTCP(this, sertopPath);
    this.serapis.push(worker);
    return worker;
  }

  /**
   * On message received
   * @param {Buffer} rawBuffer the message from the socket
   */
  handleBuffer(rawBuffer) {
    if (this.partialBuffer !== null) {
      rawBuffer = Buffer.concat([this.partialBuffer, rawBuffer]);
      this.partialBuffer = null;
    }


    while (rawBuffer.length > 0) {
      if (this.charLeftToRead > 0) {
        // still getting the information of a message

        const readSize = Math.min(this.charLeftToRead, rawBuffer.length);
        this.charLeftToRead -= readSize;

        this.bufferSoFar = Buffer.concat([
          this.bufferSoFar,
          rawBuffer.slice(0, readSize),
        ]);

        rawBuffer = rawBuffer.slice(readSize);

        if (this.charLeftToRead <= 0) {
          this.handleMessage(
              this.bufferToString(this.bufferSoFar)
          );
          this.charLeftToRead = -1;
          this.bufferSoFar = null;
          continue;
        } else {
          break;
        }
      }

      if (rawBuffer.length < INT_SIZE) {
        break;
      }

      const nextMessageLength = rawBuffer.readInt32BE(0);

      const bufferSize = rawBuffer.length - INT_SIZE;

      if (nextMessageLength > bufferSize) {
        this.charLeftToRead = nextMessageLength - bufferSize;
        this.bufferSoFar = rawBuffer.slice(INT_SIZE);
        return;
      } else {
        const endOfMessage = INT_SIZE + nextMessageLength;
        this.handleMessage(
            this.bufferToString(rawBuffer.slice(INT_SIZE, endOfMessage)));
        rawBuffer = rawBuffer.slice(endOfMessage);
      }
    }

    if (rawBuffer.length > 0) {
      this.partialBuffer = rawBuffer;
    }
  }

  /**
   * Convert buffer to string
   * @param {Buffer} buffer the buffer
   * @return {string} the string as output
   */
  bufferToString(buffer) {
    return buffer.toString(ENCODING);
  }

  /**
   * After receiving the full message\
   * Send it to the appropriate worker
   * @param {String} rawMessage the message as string
   */
  handleMessage(rawMessage) {
    // TODO add tests
    const message = JSON.parse(rawMessage);
    if (message.status === 'failure') {
      console.log('COMMAND FAILED:');
      console.log(message);
      return;
    }

    if (message.verb === 'create') {
      const newId = message.instance_id;
      console.log('Got new id: ' + newId);
      for (let j = 0; j < this.serapis.length; j++) {
        if (this.serapis[j].socketId < 0) {
          this.serapis[j].socketId = newId;
          break;
        }
      }
    } else {
      const serapiIndex = this.socketById(message.instance_id);
      if (message.verb === 'destroy') {
        this.serapis.splice(serapiIndex, 1);

        if (this.serapis.length === 0 && this.disconnecting !== null) {
          this.allStopped();
        }
      } else {
        this.serapis[serapiIndex].handleMessage(message.content);
      }
    }
  }


  /**
   * Get the socket per id
   * @param {Integer} id the id to look for
   * @return {Integer} the index
   */
  socketById(id) {
    for (let i = 0; i < this.serapis.length; i++) {
      if (this.serapis[i].socketId === id) {
        return i;
      }
    }
    console.warn(`No serapi tcp with id: ${id}`);
    return -1;
  }

  /**
   * Send a message along the socket
   * @param {String} message the message to send
   */
  async sendMessage(message) {
    const release = await this.writeLock.acquire();

    const messageBuffer = Buffer.from(message, ENCODING);
    const sizeBuffer = Buffer.alloc(4);
    sizeBuffer.writeInt32BE(messageBuffer.length);

    ipc.of[this.socketId].emit(sizeBuffer);
    ipc.of[this.socketId].emit(messageBuffer);

    release();
  }

  /**
   * Terminate all sertops
   * And after that disconnect
   * @param {Function} onShutDown function to call after shutdown (or null)
   */
  stopAll(onShutDown) {
    if (this.disconnecting !== null) {
      console.log('Already shutting down...');
      return;
    }
    this.disconnecting = onShutDown;
    for (const serapi of this.serapis) {
      if (serapi.socketId >= 0) {
        serapi.terminate();
      }
    }
  }

  /**
   * And call the callback once everything is stopped
   */
  allStopped() {
    if (this.disconnecting !== null) {
      this.disconnecting();
      this.disconnecting = null;
    }
  }
}

export default TCPManager;
