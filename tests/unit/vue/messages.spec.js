import MessagesWindow from '@/editpage/components/response/MessagesWindow';
const chai = require('chai');
const expect = chai.expect;
import {shallowMount} from '@vue/test-utils';
import Vue from 'vue';

describe('Response messages', () => {
  it('should put a new message into the queue when event emitted', async () => {
    const bus = new Vue;
    const wrapper = shallowMount(MessagesWindow, {
      propsData: {
        eventBus: bus,
        addError: {
          message: '',
        },
        ready: true,
      },
    });


    expect(wrapper.vm.messages).to.be.an('array').that.has.length(0);

    const messageText = 'New message from bus';

    bus.$emit('on-coq-message', messageText);

    await Vue.nextTick();

    expect(wrapper.vm.messages).to.be.an('array').that.has.length(1);

    expect(wrapper.find('.messageText').text()).to.include(messageText);
  });

  it('should clear the queue when clear is called', (done) => {
    const bus = new Vue;
    const wrapper = shallowMount(MessagesWindow, {
      propsData: {
        eventBus: bus,
        addError: {
          message: '',
        },
        ready: true,
      },
    });

    expect(wrapper.vm.messages).to.be.an('array').that.has.length(0);
    bus.$emit('on-coq-message', 'testMessage');
    bus.$emit('on-coq-message', 'testMessage');
    bus.$emit('on-coq-message', 'testMessage');
    expect(wrapper.vm.messages).to.be.an('array').that.has.length(3);

    bus.$emit('clear-messages');

    expect(wrapper.vm.messages).to.be.an('array').that.has.length(0);
    done();
  });

  it('should remove the right message when removeMessage is called', (done) => {
    const bus = new Vue;
    const wrapper = shallowMount(MessagesWindow, {
      propsData: {
        eventBus: bus,
        addError: {
          message: '',
        },
        ready: true,
      },
    });

    expect(wrapper.vm.messages).to.be.an('array').that.has.length(0);
    bus.$emit('on-coq-message', '0');
    bus.$emit('on-coq-message', 'toRemove');
    bus.$emit('on-coq-message', '1');
    expect(wrapper.vm.messages).to.be.an('array').that.has.length(3);
    expect(wrapper.vm.messages[1].text).to.include('toRemove');

    wrapper.vm.removeMessage(1);
    expect(wrapper.vm.messages).to.be.an('array').that.has.length(2);

    expect(wrapper.vm.messages[0].text).to.include('0');
    expect(wrapper.vm.messages[1].text).to.include('1');
    done();
  });

  it('should not have a message when there is an addError', async () => {
    const bus = new Vue;
    const wrapper = shallowMount(MessagesWindow, {
      propsData: {
        eventBus: bus,
        addError: {
          message: '',
        },
        ready: true,
        addErrorTimeout: 0,
      },
    });

    expect(wrapper.vm.messages).to.be.an('array').that.has.length(0);
    expect(wrapper.find('.message-error').exists()).to.equal(false);

    const errorMessage ='Add error occurred';

    await wrapper.setProps({
      addError: {
        message: {
          message: errorMessage,
        },
      },
    });

    expect(wrapper.vm.messages).to.be.an('array').that.has.length(0);

    expect(wrapper.find('.message-error').exists()).to.equal(true);

    expect(wrapper.find('.message-error').text()).to.include(errorMessage);
  });

  it('should not show messages until ready', async () => {
    const bus = new Vue;
    const wrapper = shallowMount(MessagesWindow, {
      propsData: {
        eventBus: bus,
        addError: {
          message: '',
        },
        ready: false,
      },
    });

    expect(wrapper.find('.messages').exists()).to.equal(false);

    const messageText = 'test message';
    bus.$emit('on-coq-message', messageText);

    await Vue.nextTick();

    expect(wrapper.vm.messages).to.be.an('array').that.has.length(1);

    expect(wrapper.find('.messages').exists()).to.equal(false);
    expect(wrapper.find('.message').exists()).to.equal(false);

    await wrapper.setProps({
      ready: true,
    });

    expect(wrapper.find('.messages').exists()).to.equal(true);
    expect(wrapper.find('.message').exists()).to.equal(true);
    expect(wrapper.find('.message').text()).to.include(messageText);
  });
});
