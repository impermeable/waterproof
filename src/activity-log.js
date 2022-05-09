import {ipcRenderer} from 'electron';

/**
 * Write message to activity log (eventually)
 * @param {String} type type of message to write
 * @param {{}} details the details of the message
 */
export function writeActivity(type, details = {}) {
  ipcRenderer.send('activity', Object.assign({type}, details));
}
