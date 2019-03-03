const path = require('path');
const {isMainThread} = require('worker_threads');
const {process} = global;

const symbols = require('./symbols');

const exokitNode = isMainThread ?
  require(path.join(__dirname, '..', 'build', 'Release', 'exokit.node'))
:
  requireNative('exokit.node');
const {nativeWindow} = exokitNode;
const webGlToOpenGl = require('webgl-to-opengl');
const GlobalContext = require('./GlobalContext');

const nativeWorker = require('worker-native');
nativeWindow.setEventLoop(nativeWorker.getEventLoop());
if (typeof requireNative === 'undefined') {
  nativeWorker.setNativeRequire('exokit.node', exokitNode.initFunctionAddress);
}

const bindings = {};
for (const k in exokitNode) {
  bindings[k] = exokitNode[k];
}
const _decorateGlIntercepts = gl => {
  gl.createShader = (createShader => function(type) {
    const result = createShader.call(this, type);
    result.type = type;
    return result;
  })(gl.createShader);
  gl.shaderSource = (shaderSource => function(shader, source) {
    if (shader.type === gl.VERTEX_SHADER) {
      source = webGlToOpenGl.vertex(source);
    } else if (shader.type === gl.FRAGMENT_SHADER) {
      source = webGlToOpenGl.fragment(source);
    }
    return shaderSource.call(this, shader, source);
  })(gl.shaderSource);
  gl.getActiveAttrib = (getActiveAttrib => function(program, index) {
    const result = getActiveAttrib.call(this, program, index);
    if (result) {
      result.name = webGlToOpenGl.unmapName(result.name);
    }
    return result;
  })(gl.getActiveAttrib);
  gl.getActiveUniform = (getActiveUniform => function(program, index) {
    const result = getActiveUniform.call(this, program, index);
    if (result) {
      result.name = webGlToOpenGl.unmapName(result.name);
    }
    return result;
  })(gl.getActiveUniform);
  gl.getAttribLocation = (getAttribLocation => function(program, path) {
    path = webGlToOpenGl.mapName(path);
    return getAttribLocation.call(this, program, path);
  })(gl.getAttribLocation);
  gl.getUniformLocation = (getUniformLocation => function(program, path) {
    path = webGlToOpenGl.mapName(path);
    return getUniformLocation.call(this, program, path);
  })(gl.getUniformLocation);
  gl.setCompatibleXRDevice = () => Promise.resolve();
};
const _onGl3DConstruct = (gl, canvas) => {
  const canvasWidth = canvas.width || innerWidth;
  const canvasHeight = canvas.height || innerHeight;

  gl.canvas = canvas;

  const document = canvas.ownerDocument;
  const window = document.defaultView;

  const windowSpec = (() => {
    if (!window[symbols.optionsSymbol].args.headless) {
      try {
        const visible = document.documentElement.contains(canvas);
        const {hidden} = document;
        const sharedWindowHandle = Array.from(GlobalContext.xrState.windowHandle);
        const title = `Exokit ${GlobalContext.version}`;
        const windowHandle = global.runSyncTop(`(() => {
          const {
            canvasWidth,
            canvasHeight,
            visible,
            hidden,
            sharedWindowHandle,
            title,
          } = global._;
          const windowHandle = nativeBindings.nativeWindow.createWindowHandle(canvasWidth, canvasHeight, visible && !hidden, sharedWindowHandle);
          nativeBindings.nativeWindow.setWindowTitle(windowHandle, title);
          return windowHandle;
        })()`, {
          canvasWidth,
          canvasHeight,
          visible,
          hidden,
          sharedWindowHandle,
          title,
        });
        return nativeWindow.initWindow3D(windowHandle, gl);
      } catch (err) {
        console.warn(err.stack);
        return null;
      }
    } else {
      return null;
    }
  })();

  if (windowSpec) {
    const [windowHandle, sharedFramebuffer, sharedColorTexture, sharedDepthStencilTexture, sharedMsFramebuffer, sharedMsColorTexture, sharedMsDepthStencilTexture, vao] = windowSpec;

    gl.setWindowHandle(windowHandle);
    gl.setDefaultVao(vao);
    nativeWindow.setEventHandler(windowHandle, (type, data) => {
      switch (type) {
        case 'focus': {
          const {focused} = data;
          if (!focused && window.top.document.pointerLockElement) {
            window.top.document.exitPointerLock();
          }
          break;
        }
        case 'framebufferResize': {
          const {width, height} = data;
          // innerWidth = width;
          // innerHeight = height;

          window.innerWidth = width / window.devicePixelRatio;
          window.innerHeight = height / window.devicePixelRatio;
          window.dispatchEvent(new window.Event('resize'));
          break;
        }
        case 'keydown': {
          let handled = false;
          if (data.keyCode === 27) { // ESC
            if (window.top.document.pointerLockElement) {
              window.top.document.exitPointerLock();
              handled = true;
            }
            if (window.top.document.fullscreenElement) {
              window.top.document.exitFullscreen();
              handled = true;
            }
          }
          if (data.keyCode === 122) { // F11
            if (window.top.document.fullscreenElement) {
              window.top.document.exitFullscreen();
              handled = true;
            } else {
              window.top.document.requestFullscreen();
              handled = true;
            }
          }

          if (!handled) {
            canvas.dispatchEvent(new window.KeyboardEvent(type, data));
          }
          break;
        }
        case 'keyup':
        case 'keypress': {
          canvas.dispatchEvent(new window.KeyboardEvent(type, data));
          break;
        }
        case 'mousedown':
        case 'mouseup':
        case 'click': {
          canvas.dispatchEvent(new window.MouseEvent(type, data));
          break;
        }
        case 'wheel': {
          canvas.dispatchEvent(new window.WheelEvent(type, data));
          break;
        }
        case 'mousemove': {
          canvas.dispatchEvent(new window.MouseEvent(type, data));
          break;
        }
        case 'drop': {
          const _readFiles = paths => {
            const result = [];

            return Promise.all(paths.map(p =>
              new Promise((accept, reject) => {
                fs.lstat(p, (err, stats) => {
                  if (!err) {
                    if (stats.isFile()) {
                      fs.readFile(p, (err, data) => {
                        if (!err) {
                          const file = new window.Blob([data]);
                          file.name = path.basename(p);
                          file.path = p;
                          result.push(file);

                          accept();
                        } else {
                          reject(err);
                        }
                      });
                    } else if (stats.isDirectory()) {
                      fs.readdir(p, (err, fileNames) => {
                        if (!err) {
                          _readFiles(fileNames.map(fileName => path.join(p, fileName)))
                            .then(files => {
                              result.push.apply(result, files);

                              accept();
                            })
                            .catch(err => {
                              reject(err);
                            });
                        } else {
                          reject(err);
                        }
                      });
                    } else {
                      accept();
                    }
                  } else {
                    reject(err);
                  }
                });
              })
            ))
              .then(() => result);
          };

          _readFiles(data.paths)
            .then(files => {
              const dataTransfer = new window.DataTransfer({
                files,
              });
              const e = new window.DragEvent('drop');
              e.dataTransfer = dataTransfer;
              canvas.dispatchEvent(e);
            })
            .catch(err => {
              console.warn(err.stack);
            });
          break;
        }
        case 'quit': {
          gl.destroy();
          break;
        }
      }
    });

    const nativeWindowSize = nativeWindow.getFramebufferSize(windowHandle);
    const nativeWindowHeight = nativeWindowSize.height;
    const nativeWindowWidth = nativeWindowSize.width;

    // Calculate devicePixelRatio.
    window.devicePixelRatio = nativeWindowWidth / canvasWidth;

    // Tell DOM how large the window is.
    // window.innerHeight = nativeWindowHeight / window.devicePixelRatio;
    // window.innerWidth = nativeWindowWidth / window.devicePixelRatio;

    const {hidden} = document;
    if (hidden) {
      const [fbo, tex, depthTex, msFbo, msTex, msDepthTex] = nativeWindow.createRenderTarget(gl, canvasWidth, canvasHeight, sharedColorTexture, sharedDepthStencilTexture, sharedMsColorTexture, sharedMsDepthStencilTexture);

      gl.setDefaultFramebuffer(msFbo);

      gl.resize = (width, height) => { // XXX run these on the main thread
        nativeWindow.setCurrentWindowContext(windowHandle);
        nativeWindow.resizeRenderTarget(gl, width, height, fbo, tex, depthTex, msFbo, msTex, msDepthTex);
        
        window.windowEmit('resize', {
          width,
          height,
        });
      };

      window.windowEmit('resize', {
        width: canvas.width,
        height: canvas.height,
      });
      window.windowEmit('framebuffer', {
        msFbo,
        msTex,
        msDepthTex,
        fbo,
        tex,
        depthTex,
      });
    } else {
      gl.resize = (width, height) => {
        nativeWindow.setCurrentWindowContext(windowHandle);
        nativeWindow.resizeRenderTarget(gl, width, height, sharedFramebuffer, sharedColorTexture, sharedDepthStencilTexture, sharedMsFramebuffer, sharedMsColorTexture, sharedMsDepthStencilTexture);
      };
    }

    const ondomchange = () => {
      process.nextTick(() => { // show/hide synchronously emits events
        if (!hidden) {
          const domVisible = canvas.ownerDocument.documentElement.contains(canvas);
          const windowVisible = nativeWindow.isVisible(windowHandle);
          if (domVisible) {
            if (!windowVisible) {
              global.runSyncTop(`(() => {
                const {
                  windowHandle,
                } = global._;
                nativeBindings.nativeWindow.show(windowHandle);
              })()`, {
                windowHandle,
              });
            }
          } else {
            if (windowVisible) {
              // XXX can run async
              global.runSyncTop(`(() => {
                const {
                  windowHandle,
                } = global._;
                nativeBindings.nativeWindow.hide(windowHandle);
              })()`, {
                windowHandle,
              });
            }
          }
        }
      });
    };
    canvas.ownerDocument.on('domchange', ondomchange);

    gl.destroy = (destroy => function() {
      destroy.call(this);

      nativeWindow.setCurrentWindowContext(windowHandle);

      if (gl.id === GlobalContext.vrPresentState.glContextId) {
        throw new Error('destroyed vr presenting context');
        /* bindings.nativeVr.VR_Shutdown();

        GlobalContext.vrPresentState.glContextId = 0;
        GlobalContext.vrPresentState.system = null;
        GlobalContext.vrPresentState.compositor = null; */
      }
      if (gl.id === GlobalContext.mlPresentState.mlGlContextId) {
        throw new Error('destroyed ml presenting context');
        // GlobalContext.mlPresentState.mlGlContextId = 0;
      }

      global.runSyncTop(`(() => {
        const {
          windowHandle,
        } = global._;
        nativeBindings.nativeWindow.destroy(windowHandle);
      })()`, {
        windowHandle,
      });
      canvas._context = null;

      if (hidden) {
        window.windowEmit('framebuffer', null);
      }
      canvas.ownerDocument.removeListener('domchange', ondomchange);

      GlobalContext.contexts.splice(GlobalContext.contexts.indexOf(gl), 1);

      if (gl.id === 1) {
        process.kill(process.pid); // XXX make this a softer process.exit()
      }
    })(gl.destroy);
    
    gl.id = Atomics.add(GlobalContext.xrState.id, 0) + 1;
    GlobalContext.contexts.push(gl);
  } else {
    gl.destroy();
  }
};
bindings.nativeGl = (nativeGl => {
  function WebGLRenderingContext(canvas) {
    const gl = new nativeGl();
    _decorateGlIntercepts(gl);
    _onGl3DConstruct(gl, canvas);
    return gl;
  }
  for (const k in nativeGl) {
    WebGLRenderingContext[k] = nativeGl[k];
  }
  return WebGLRenderingContext;
})(bindings.nativeGl);
bindings.nativeGl2 = (nativeGl2 => {
  function WebGL2RenderingContext(canvas) {
    const gl = new nativeGl2();
    _decorateGlIntercepts(gl);
    _onGlConstruct(gl, canvas);
    return gl;
  }
  for (const k in nativeGl2) {
    WebGL2RenderingContext[k] = nativeGl2[k];
  }
  return WebGL2RenderingContext;
})(bindings.nativeGl2);

const _onGl2DConstruct = (ctx, canvas) => {
  const canvasWidth = canvas.width || innerWidth;
  const canvasHeight = canvas.height || innerHeight;

  ctx.canvas = canvas;

  const window = canvas.ownerDocument.defaultView;

  const windowSpec = (() => {
    if (!window[symbols.optionsSymbol].args.headless) {
      try {
        const sharedWindowHandle = Array.from(GlobalContext.xrState.windowHandle);
        const windowHandle = global.runSyncTop(`(() => {
          const {
            canvasWidth,
            canvasHeight,
            sharedWindowHandle,
          } = global._;
          return nativeBindings.nativeWindow.createWindowHandle(canvasWidth, canvasHeight, false, sharedWindowHandle);
        })()`, {
          canvasWidth,
          canvasHeight,
          sharedWindowHandle,
        });
        return nativeWindow.initWindow2D(windowHandle);
      } catch (err) {
        console.warn(err.message);
        return null;
      }
    } else {
      return null;
    }
  })();

  if (windowSpec) {
    const [windowHandle, tex] = windowSpec;

    ctx.setWindowHandle(windowHandle);
    ctx.setTexture(tex, canvasWidth, canvasHeight);
    
    ctx.destroy = (destroy => function() {
      destroy.call(this);
      
      nativeWindow.destroy(windowHandle);
      canvas._context = null;
      
      window.postInternalMessage({
        type: 'postRequestAsync',
        method: 'context.destroy',
        args: {
          id,
        },
      });
      GlobalContext.contexts.splice(GlobalContext.contexts.indexOf(ctx), 1);
    })(ctx.destroy);
    
    ctx.id = Atomics.add(GlobalContext.xrState.id, 0) + 1;
    GlobalContext.contexts.push(ctx);
  } else {
    ctx.destroy();
  }
};
bindings.nativeCanvasRenderingContext2D = (nativeCanvasRenderingContext2D => {
  function CanvasRenderingContext2D(canvas) {
    const ctx = new nativeCanvasRenderingContext2D();
    _onGl2DConstruct(ctx, canvas);
    return ctx;
  }
  for (const k in nativeCanvasRenderingContext2D) {
    CanvasRenderingContext2D[k] = nativeCanvasRenderingContext2D[k];
  }
  return CanvasRenderingContext2D;
})(bindings.nativeCanvasRenderingContext2D);
GlobalContext.CanvasRenderingContext2D = bindings.nativeCanvasRenderingContext2D;
GlobalContext.WebGLRenderingContext = bindings.nativeGl;
GlobalContext.WebGL2RenderingContext = bindings.nativeGl2;

bindings.nativeAudio.AudioContext = (OldAudioContext => class AudioContext extends OldAudioContext {
  decodeAudioData(arrayBuffer, successCallback, errorCallback) {
    return new Promise((resolve, reject) => {
      try {
        let audioBuffer = this._decodeAudioDataSync(arrayBuffer);
        if (successCallback) {
          process.nextTick(() => {
            try {
              successCallback(audioBuffer);
            } catch(err) {
              console.warn(err);
            }
          });
        }
        resolve(audioBuffer);
      } catch(err) {
        console.warn(err);
        if (errorCallback) {
          process.nextTick(() => {
            try {
              errorCallback(err);
            } catch(err) {
              console.warn(err);
            }
          });
        }
        reject(err);
      }
    });
  }
})(bindings.nativeAudio.AudioContext);

bindings.nativeAudio.PannerNode.setPath(path.join(require.resolve('native-audio-deps').slice(0, -'index.js'.length), 'assets', 'hrtf'));

bindings.nativeWorker = nativeWorker;

if (bindings.nativeOpenVR) {
	bindings.nativeOpenVR.EVRInitError = {
	  None: 0,
	  Unknown: 1,

	  Init_InstallationNotFound: 100,
	  Init_InstallationCorrupt: 101,
	  Init_VRClientDLLNotFound: 102,
	  Init_FileNotFound: 103,
	  Init_FactoryNotFound: 104,
	  Init_InterfaceNotFound: 105,
	  Init_InvalidInterface: 106,
	  Init_UserConfigDirectoryInvalid: 107,
	  Init_HmdNotFound: 108,
	  Init_NotInitialized: 109,
	  Init_PathRegistryNotFound: 110,
	  Init_NoConfigPath: 111,
	  Init_NoLogPath: 112,
	  Init_PathRegistryNotWritable: 113,
	  Init_AppInfoInitFailed: 114,
	  Init_Retry: 115,
	  Init_InitCanceledByUser: 116,
	  Init_AnotherAppLaunching: 117,
	  Init_SettingsInitFailed: 118,
	  Init_ShuttingDown: 119,
	  Init_TooManyObjects: 120,
	  Init_NoServerForBackgroundApp: 121,
	  Init_NotSupportedWithCompositor: 122,
	  Init_NotAvailableToUtilityApps: 123,
	  Init_Internal: 124,
	  Init_HmdDriverIdIsNone: 125,
	  Init_HmdNotFoundPresenceFailed: 126,
	  Init_VRMonitorNotFound: 127,
	  Init_VRMonitorStartupFailed: 128,
	  Init_LowPowerWatchdogNotSupported: 129,
	  Init_InvalidApplicationType: 130,
	  Init_NotAvailableToWatchdogApps: 131,
	  Init_WatchdogDisabledInSettings: 132,
	  Init_VRDashboardNotFound: 133,
	  Init_VRDashboardStartupFailed: 134,

	  Driver_Failed: 200,
	  Driver_Unknown: 201,
	  Driver_HmdUnknown: 202,
	  Driver_NotLoaded: 203,
	  Driver_RuntimeOutOfDate: 204,
	  Driver_HmdInUse: 205,
	  Driver_NotCalibrated: 206,
	  Driver_CalibrationInvalid: 207,
	  Driver_HmdDisplayNotFound: 208,
	  Driver_TrackedDeviceInterfaceUnknown: 209,
	  Driver_HmdDriverIdOutOfBounds: 211,
	  Driver_HmdDisplayMirrored: 212,

	  IPC_ServerInitFailed: 300,
	  IPC_ConnectFailed: 301,
	  IPC_SharedStateInitFailed: 302,
	  IPC_CompositorInitFailed: 303,
	  IPC_MutexInitFailed: 304,
	  IPC_Failed: 305,
	  IPC_CompositorConnectFailed: 306,
	  IPC_CompositorInvalidConnectResponse: 307,
	  IPC_ConnectFailedAfterMultipleAttempts: 308,

	  Compositor_Failed: 400,
	  Compositor_D3D11HardwareRequired: 401,
	  Compositor_FirmwareRequiresUpdate: 402,
	  Compositor_OverlayInitFailed: 403,
	  Compositor_ScreenshotsInitFailed: 404,

	  VendorSpecific_UnableToConnectToOculusRuntime: 1000,

	  VendorSpecific_HmdFound_CantOpenDevice: 1101,
	  VendorSpecific_HmdFound_UnableToRequestConfigStart: 1102,
	  VendorSpecific_HmdFound_NoStoredConfig: 1103,
	  VendorSpecific_HmdFound_ConfigTooBig: 1104,
	  VendorSpecific_HmdFound_ConfigTooSmall: 1105,
	  VendorSpecific_HmdFound_UnableToInitZLib: 1106,
	  VendorSpecific_HmdFound_CantReadFirmwareVersion: 1107,
	  VendorSpecific_HmdFound_UnableToSendUserDataStart: 1108,
	  VendorSpecific_HmdFound_UnableToGetUserDataStart: 1109,
	  VendorSpecific_HmdFound_UnableToGetUserDataNext: 1110,
	  VendorSpecific_HmdFound_UserDataAddressRange: 1111,
	  VendorSpecific_HmdFound_UserDataError: 1112,
	  VendorSpecific_HmdFound_ConfigFailedSanityCheck: 1113,

	  Steam_SteamInstallationNotFound: 2000,
	};

	bindings.nativeOpenVR.EVRApplicationType = {
	  Other: 0,
	  Scene: 1,
	  Overlay: 2,
	  Background: 3,
	  Utility: 4,
	  VRMonitor: 5,
	  SteamWatchdog: 6,
	  Bootstrapper: 7,
	};

	bindings.nativeOpenVR.EVREye = {
	  Left: 0,
	  Right: 1,
	};

	bindings.nativeOpenVR.ETrackingUniverseOrigin = {
	  Seated: 0,
	  Standing: 1,
	  RawAndUncalibrated: 2,
	};

	bindings.nativeOpenVR.ETrackingResult = {
	  Uninitialized: 1,
	  Calibrating_InProgress: 100,
	  Calibrating_OutOfRange: 101,
	  Running_OK: 200,
	  Running_OutOfRange: 201,
	};

	bindings.nativeOpenVR.ETrackedDeviceClass = {
	  Invalid: 0,
	  HMD: 1,
	  Controller: 2,
	  GenericTracker: 3,
	  TrackingReference: 4,
	  DisplayRedirect: 5,
	};
}

GlobalContext.nativeOculusVR = bindings.nativeOculusVR;
GlobalContext.nativeOpenVR = bindings.nativeOpenVR;
GlobalContext.nativeMl = bindings.nativeMl;
GlobalContext.nativeBrowser = bindings.nativeBrowser;
GlobalContext.nativeOculusVR = bindings.nativeOculusVR;

if (bindings.nativeOculusVR) {
  bindings.nativeOculusVR.requestPresent = function (layers) {
    const layer = layers.find(layer => layer && layer.source && layer.source.tagName === 'CANVAS');
    if (layer) {
      const canvas = layer.source;
      if (!vrPresentState.glContext) {
        let context = canvas._context;
        if (!(context && context.constructor && context.constructor.name === 'WebGLRenderingContext')) {
          context = canvas.getContext('webgl');
        }
        const window = canvas.ownerDocument.defaultView;

        const windowHandle = context.getWindowHandle();
        nativeBindings.nativeWindow.setCurrentWindowContext(windowHandle);

        const system = vrPresentState.system = vrPresentState.system || bindings.nativeOculusVR.Oculus_Init();
        const lmContext = vrPresentState.lmContext || (nativeBindings.nativeLm && new nativeBindings.nativeLm());

        const {width: halfWidth, height} = system.GetRecommendedRenderTargetSize();
        const MAX_TEXTURE_SIZE = 4096;
        const MAX_TEXTURE_SIZE_HALF = MAX_TEXTURE_SIZE/2;
        if (halfWidth > MAX_TEXTURE_SIZE_HALF) {
          const factor = halfWidth / MAX_TEXTURE_SIZE_HALF;
          halfWidth = MAX_TEXTURE_SIZE_HALF;
          height = Math.floor(height / factor);
        }
        const width = halfWidth * 2;
        xrState.renderWidth[0] = halfWidth;
        xrState.renderHeight[0] = height;

        const cleanups = [];

        const [fbo, tex, depthTex, msFbo, msTex, msDepthTex] = nativeBindings.nativeWindow.createRenderTarget(context, width, height, 0, 0, 0, 0);

        context.setDefaultFramebuffer(msFbo);

        vrPresentState.isPresenting = true;
        vrPresentState.oculusSystem = system;
        vrPresentState.glContext = context;
        vrPresentState.msFbo = msFbo;
        vrPresentState.msTex = msTex;
        vrPresentState.msDepthTex = msDepthTex;
        vrPresentState.fbo = fbo;
        vrPresentState.tex = tex;
        vrPresentState.depthTex = depthTex;
        vrPresentState.cleanups = cleanups;

        vrPresentState.lmContext = lmContext;

        canvas.framebuffer = {
          width,
          height,
          msFbo,
          msTex,
          msDepthTex,
          fbo,
          tex,
          depthTex,
        };

        const _attribute = (name, value) => {
          if (name === 'width' || name === 'height') {
            nativeBindings.nativeWindow.setCurrentWindowContext(windowHandle);

            nativeBindings.nativeWindow.resizeRenderTarget(context, canvas.width, canvas.height, fbo, tex, depthTex, msFbo, msTex, msDepthTex);
          }
        };
        canvas.on('attribute', _attribute);
        cleanups.push(() => {
          canvas.removeListener('attribute', _attribute);
        });

        /* window.top.updateVrFrame({
          renderWidth: xrState.renderWidth[0],
          renderHeight: xrState.renderHeight[0],
          force: true,
        }); */

        return canvas.framebuffer;
      } else if (canvas.ownerDocument.framebuffer) {
        const {width, height} = canvas;
        const {msFbo, msTex, msDepthTex, fbo, tex, depthTex} = canvas.ownerDocument.framebuffer;
        return {
          width,
          height,
          msFbo,
          msTex,
          msDepthTex,
          fbo,
          tex,
          depthTex,
        };
      } else {
        /* const {width: halfWidth, height} = vrPresentState.system.GetRecommendedRenderTargetSize();
        const width = halfWidth * 2; */

        const {msFbo, msTex, msDepthTex, fbo, tex, depthTex} = vrPresentState;
        return {
          width: xrState.renderWidth[0] * 2,
          height: xrState.renderHeight[0],
          msFbo,
          msTex,
          msDepthTex,
          fbo,
          tex,
          depthTex,
        };
      }
    } else {
      throw new Error('no HTMLCanvasElement source provided');
    }
  }
  bindings.exitPresent = function () {
    return Promise.resolve();
  };
}

if (bindings.nativeOpenVR) {
  const cleanups = [];
  bindings.nativeOpenVR.requestPresent = async function(layers) {
    const layer = layers.find(layer => layer && layer.source && layer.source.tagName === 'CANVAS');
    if (layer) {
      const canvas = layer.source;

      const presentSpec = (() => {
        const {xrState} = GlobalContext;
        
        if (!xrState.isPresenting[0]) {
          const vrContext = bindings.nativeVr.getContext();
          const system = bindings.nativeVr.VR_Init(bindings.nativeVr.EVRApplicationType.Scene);
          const compositor = vrContext.compositor.NewCompositor();

          // const lmContext = vrPresentState.lmContext || (nativeLm && new nativeLm());

          vrPresentState.vrContext = vrContext;
          vrPresentState.system = system;
          vrPresentState.compositor = compositor;

          let {width: halfWidth, height} = system.GetRecommendedRenderTargetSize();
          const MAX_TEXTURE_SIZE = 4096;
          const MAX_TEXTURE_SIZE_HALF = MAX_TEXTURE_SIZE/2;
          if (halfWidth > MAX_TEXTURE_SIZE_HALF) {
            const factor = halfWidth / MAX_TEXTURE_SIZE_HALF;
            halfWidth = MAX_TEXTURE_SIZE_HALF;
            height = Math.floor(height / factor);
          }
          const width = halfWidth * 2;

          return Promise.resolve({
            wasPresenting: false,
            width,
            height,
          });
        } else {
          const {msFbo, msTex, msDepthTex, fbo, tex, depthTex} = vrPresentState;
          return Promise.resolve({
            wasPresenting: true,
            width: xrState.renderWidth[0] * 2,
            height: xrState.renderHeight[0],
            msFbo,
            msTex,
            msDepthTex,
            fbo,
            tex,
            depthTex,
          });
        }
      })();

      if (!presentSpec.wasPresenting) {
        let context = canvas._context;
        if (!(context && context.constructor && context.constructor.name === 'WebGLRenderingContext')) {
          context = canvas.getContext('webgl');
        }
        const window = canvas.ownerDocument.defaultView;

        const {width, height} = presentSpec;
        
        const windowHandle = context.getWindowHandle();
        nativeWindow.setCurrentWindowContext(windowHandle);

        const [fbo, tex, depthTex, msFbo, msTex, msDepthTex] = nativeWindow.createRenderTarget(context, width, height, 0, 0, 0, 0);

        // vrPresentState.lmContext = lmContext;

        const framebuffer = {
          width,
          height,
          msFbo,
          msTex,
          msDepthTex,
          fbo,
          tex,
          depthTex,
        };

        xrState.isPresenting[0] = 1;
        const halfWidth = width/2;
        xrState.renderWidth[0] = halfWidth;
        xrState.renderHeight[0] = height;

        const context = GlobalContext.contexts.find(context => context.window === window && context.id === id);
        context.framebuffer = framebuffer;
        vrPresentState.glContextId = context.id;
        vrPresentState.msFbo = msFbo;
        vrPresentState.msTex = msTex;
        vrPresentState.msDepthTex = msDepthTex;
        vrPresentState.fbo = fbo;
        vrPresentState.tex = tex;
        vrPresentState.depthTex = depthTex;
        
        context.setDefaultFramebuffer(msFbo);

        const _attribute = (name, value) => {
          if (name === 'width' || name === 'height') {
            nativeWindow.setCurrentWindowContext(windowHandle);

            nativeWindow.resizeRenderTarget(context, canvas.width, canvas.height, fbo, tex, depthTex, msFbo, msTex, msDepthTex);
          }
        };
        canvas.on('attribute', _attribute);
        cleanups.push(() => {
          canvas.removeListener('attribute', _attribute);
        });

        return framebuffer;
      } else if (canvas.ownerDocument.framebuffer) {
        const {width, height} = canvas;
        const {msFbo, msTex, msDepthTex, fbo, tex, depthTex} = canvas.ownerDocument.framebuffer;
        return {
          width,
          height,
          msFbo,
          msTex,
          msDepthTex,
          fbo,
          tex,
          depthTex,
        };
      } else {
        return presentSpec;
        /* const {msFbo, msTex, msDepthTex, fbo, tex, depthTex} = vrPresentState;
        return {
          width: xrState.renderWidth[0] * 2,
          height: xrState.renderHeight[0],
          msFbo,
          msTex,
          msDepthTex,
          fbo,
          tex,
          depthTex,
        }; */
      }
    } else {
      throw new Error('no HTMLCanvasElement source provided');
    }
  };
  bindings.nativeOpenVR.exitPresent = async function() {
    if (vrPresentState.vrContext) {
      bindings.nativeVr.VR_Shutdown();
      
      const {msFbo, msTex, msDepthTex, fbo, tex, depthTex} = vrPresentState;

      vrPresentState.vrContext = null;
      vrPresentState.system = null;
      vrPresentState.compositor = null;
      vrPresentState.glContextId = 0;
      vrPresentState.msFbo = null;
      vrPresentState.msTex = null;
      vrPresentState.msDepthTex = null;
      vrPresentState.fbo = null;
      vrPresentState.tex = null;
      vrPresentState.depthTex = null;

      nativeWindow.destroyRenderTarget(msFbo, msTex, msDepthStencilTex);
      nativeWindow.destroyRenderTarget(fbo, tex, msDepthTex);

      const context = GlobalContext.contexts.find(contex => contex.id === vrPresentState.glContextId);
      nativeWindow.setCurrentWindowContext(context.getWindowHandle());
      context.setDefaultFramebuffer(0);

      for (let i = 0; i < cleanups.length; i++) {
        cleanups[i]();
      }
      cleanups.length = 0;
    }
  };
}

if (bindings.nativeMl) {
  let canvas = null;
  const cleanups = [];
  bindings.nativeMl.requestPresent = async function(layers) {
    const layer = layers.find(layer => layer && layer.source && layer.source.tagName === 'CANVAS');
    if (layer) {
      canvas = layer.source;
      let context = canvas._context;
      if (!(context && context.constructor && context.constructor.name === 'WebGLRenderingContext')) {
        context = canvas.getContext('webgl');
      }
      
      const presentSpec = (() => {
        const {mlPresentState} = GlobalContext;

        if (!xrState.isPresenting[0]) {
          mlPresentState.mlContext = new bindings.nativeMl();
          mlPresentState.mlContext.Present(windowHandle, context);

          const {width: halfWidth, height} = mlPresentState.mlContext.GetSize();
          const width = halfWidth * 2;
          
          return {
            wasPresenting: false,
            width,
            height,
          };
        } else {
          const {mlMsFbo: msFbo, mlMsTex: msTex, mlMsDepthTex: msDepthTex, mlFbo: fbo, mlTex: tex, mlDepthTex: depthTex} = mlPresentState;
          return {
            wasPresenting: true,
            width: xrState.renderWidth[0] * 2,
            height: xrState.renderHeight[0],
            msFbo,
            msTex,
            msDepthTex,
            fbo,
            tex,
            depthTex,
          };
        }
      })();

      if (!presentSpec.wasPresenting) {
        const {width, height} = presentSpec;

        const windowHandle = context.getWindowHandle();
        nativeWindow.setCurrentWindowContext(windowHandle);

        xrState.isPresenting[0] = 1;
        const halfWidth = width/2;
        xrState.renderWidth[0] = halfWidth;
        xrState.renderHeight[0] = height;

        const [fbo, tex, depthTex, msFbo, msTex, msDepthTex] = nativeWindow.createRenderTarget(context, width, height, 0, 0, 0, 0);

        const {mlPresentState} = GlobalContext;
        mlPresentState.mlContext.SetContentTexture(tex);

        const context = GlobalContext.contexts.find(context => context.window === window && context.id === id);
        context.framebuffer = {
          width,
          height,
          msFbo,
          msTex,
          msDepthTex,
          fbo,
          tex,
          depthTex,
        };

        mlPresentState.mlGlContextId = context.id;
        mlPresentState.mlFbo = fbo;
        mlPresentState.mlTex = tex;
        mlPresentState.mlDepthTex = depthTex;
        mlPresentState.mlMsFbo = msFbo;
        mlPresentState.mlMsTex = msTex;
        mlPresentState.mlMsDepthTex = msDepthTex

        const _attribute = (name, value) => {
          if (name === 'width' || name === 'height') {
            nativeWindow.setCurrentWindowContext(windowHandle);

            nativeWindow.resizeRenderTarget(context, canvas.width, canvas.height, fbo, tex, depthTex, msFbo, msTex, msDepthTex);
          }
        };
        canvas.on('attribute', _attribute);
        cleanups.push(() => {
          canvas.removeListener('attribute', _attribute);
        });

        context.setDefaultFramebuffer(msFbo);

        return context.framebuffer;
      } else if (canvas.ownerDocument.framebuffer) {
        const {width, height} = canvas;
        const {msFbo, msTex, msDepthTex, fbo, tex, depthTex} = canvas.ownerDocument.framebuffer;
        
        return {
          width,
          height,
          msFbo,
          msTex,
          msDepthTex,
          fbo,
          tex,
          depthTex,
        };
      } else {
        return presentSpec;
        /* return {
          width: xrState.renderWidth[0] * 2,
          height: xrState.renderHeight[0],
          msFbo: mlPresentState.mlMsFbo,
          msTex: mlPresentState.mlMsTex,
          msDepthTex: mlPresentState.mlMsDepthTex,
          fbo: mlPresentState.mlFbo,
          tex: mlPresentState.mlTex,
          depthTex: mlPresentState.mlDepthTex,
        }; */
      }
    } else {
      throw new Error('no HTMLCanvasElement source provided');
    }
  };
  bindings.nativeMl.exitPresent = async function() {
    const {mlPresentState} = GlobalContext;
      
    if (mlPresentState.mlContext) {
      mlPresentState.mlContext.Exit();
      mlPresentState.mlContext.Destroy();

      const {mlGlContextId, mlMsFbo: msFbo, mlMsTex: msTex, mlMsDepthTex: msDepthTex, mlFbo: fbo, mlTex: tex, mlDepthTex: depthTex} = mlPresentState;

      mlPresentState.mlContext = null;
      mlPresentState.mlGlContextId = 0;
      mlPresentState.mlFbo = null;
      mlPresentState.mlTex = null;
      mlPresentState.mlDepthTex = null;
      mlPresentState.mlMsFbo = null;
      mlPresentState.mlMsTex = null;
      mlPresentState.mlMsDepthTex = null;
      mlPresentState.mlCleanups = null;
      mlPresentState.mlHasPose = false;

      nativeWindow.destroyRenderTarget(mlMsFbo, msTex, msDepthTex);
      nativeWindow.destroyRenderTarget(mlFbo, mlTex, depthTex);

      const mlGlContext = GlobalContext.contexts.find(context => context.id === mlGlContextId);
      nativeWindow.setCurrentWindowContext(mlGlContext.getWindowHandle());
      mlGlContext.setDefaultFramebuffer(0);

      canvas = null;
      for (let i = 0; i < cleanups.length; i++) {
        cleanups[i]();
      }
      cleanups.length = 0;
    }
  };

  const _mlEvent = e => {
    // console.log('got ml keyboard event', e);

    const window = canvas.ownerDocument.defaultView;

    switch (e.type) {
      case 'newInitArg': {
        break;
      }
      case 'stop':
      case 'pause': {
        if (mlPresentState.mlContext) {
          mlPresentState.mlContext.Exit();
        }
        bindings.nativeMl.DeinitLifecycle();
        process.exit();
        break;
      }
      case 'resume': {
        break;
      }
      case 'unloadResources': {
        break;
      }
      case 'keydown': {
        let handled = false;
        if (e.keyCode === 27) { // ESC
          if (window.top.document.pointerLockElement) {
            window.top.document.exitPointerLock();
            handled = true;
          }
          if (window.top.document.fullscreenElement) {
            window.top.document.exitFullscreen();
            handled = true;
          }
        }
        if (e.keyCode === 122) { // F11
          if (window.top.document.fullscreenElement) {
            window.top.document.exitFullscreen();
            handled = true;
          } else {
            window.top.document.requestFullscreen();
            handled = true;
          }
        }

        if (!handled) {
          canvas.dispatchEvent(new window.KeyboardEvent(e.type, e));
        }
        break;
      }
      case 'keyup':
      case 'keypress': {
        canvas.dispatchEvent(new window.KeyboardEvent(e.type, e));
        break;
      }
      default:
        break;
    }
  };
  if (isMainThread) {
    if (!bindings.nativeMl.IsSimulated()) {
      bindings.nativeMl.InitLifecycle();
      bindings.nativeMl.SetEventHandler(_mlEvent);
    } else {
      // try to connect to MLSDK
      const MLSDK_PORT = 17955;
      const s = net.connect(MLSDK_PORT, '127.0.0.1', () => {
        s.destroy();

        bindings.nativeMl.InitLifecycle();
        bindings.nativeMl.SetEventHandler(_mlEvent);
      });
      s.on('error', () => {});
    }
  }
}

module.exports = bindings;
