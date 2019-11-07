/* eslint-disable */
//TODO write tests for vo compiler
const fs = require('fs');
const path = require('path');
const sinon = require('sinon');
const chai = require('chai');
const sandbox = sinon.createSandbox();
const expect = chai.expect;


import {VOCompiler}
  from '../../../src/io/compileToVO.js';


describe('Compiling wpn files', () => {
  beforeEach(() => {

  });

  afterEach(() => {
    sandbox.restore();
  });
});
