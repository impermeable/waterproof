import Edit from '@/editpage/Edit.vue';
const chai = require('chai');
const expect = chai.expect;
import {shallowMount} from '@vue/test-utils';
import Vue from 'vue';
Vue.use(require('vue-shortkey'));

describe('Tabs', () => {
  it('should open new tab when calling function openNewTab()', () => {
    const wrapper = shallowMount(Edit);
    const numberOfTabs = wrapper.vm.tabs.length;
    wrapper.vm.openNewTab();
    const newNumberOfTabs = wrapper.vm.tabs.length;
    expect(newNumberOfTabs).to.equal(numberOfTabs+1);
  });

  it('should close tab when calling function closeTab()', () => {
    const wrapper = shallowMount(Edit);
    wrapper.vm.openNewTab();
    wrapper.vm.openNewTab();
    const numberOfTabs = wrapper.vm.tabs.length;
    const idOfLastTab = wrapper.vm.tabs[numberOfTabs-1].id;
    wrapper.vm.closeTab(numberOfTabs-1);
    for (const tab of wrapper.vm.tabs) {
      expect(idOfLastTab === tab.id).to.equal(false);
    }
    const newNumberOfTabs = wrapper.vm.tabs.length;
    expect(newNumberOfTabs).to.equal(numberOfTabs-1);
  });
});
