const fs = require('fs');
const path = require('path');
const sinon = require('sinon');
const chai = require('chai');
const sandbox = sinon.createSandbox();
const expect = chai.expect;

import {VOCompiler}
  from '../../../src/io/compileToVO.js';


describe('Reading the configuration file', () => {
  beforeEach(() => {

  });

  afterEach(() => {
    sandbox.restore();
  });
});
