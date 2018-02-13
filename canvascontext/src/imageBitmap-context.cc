#include <canvascontext/include/imageBitmap-context.h>

using namespace v8;
using namespace node;
// using namespace std;

Handle<Object> ImageBitmap::Initialize(Isolate *isolate, Local<Value> imageCons) {
  Nan::EscapableHandleScope scope;

  // constructor
  Local<FunctionTemplate> ctor = Nan::New<FunctionTemplate>(New);
  ctor->InstanceTemplate()->SetInternalFieldCount(1);
  ctor->SetClassName(JS_STR("ImageBitmap"));

  // prototype
  // Nan::SetPrototypeMethod(ctor, "save",save);// NODE_SET_PROTOTYPE_METHOD(ctor, "save", save);
  Local<ObjectTemplate> proto = ctor->PrototypeTemplate();

  Local<Function> ctorFn = ctor->GetFunction();

  Local<Function> createImageBitmapFn = Nan::New<Function>(CreateImageBitmap);
  createImageBitmapFn->Set(JS_STR("ImageBitmap"), ctorFn);
  createImageBitmapFn->Set(JS_STR("Image"), imageCons);

  ctorFn->Set(JS_STR("createImageBitmap"), createImageBitmapFn);

  // Nan::SetAccessor(proto,JS_STR("src"), SrcGetter, SrcSetter);
  // Nan::Set(target, JS_STR("Image"), ctor->GetFunction());

  // constructor_template.Reset(Isolate::GetCurrent(), ctor->GetFunction());

  return scope.Escape(ctorFn);
}

unsigned int ImageBitmap::GetWidth() {
  return imageData->getWidth();
}

unsigned int ImageBitmap::GetHeight() {
  return imageData->getHeight();
}

unsigned int ImageBitmap::GetNumChannels() {
  return imageData->getNumChannels();
}

unsigned char *ImageBitmap::GetData() {
  return imageData->getData();
}

NAN_METHOD(ImageBitmap::New) {
  Nan::HandleScope scope;

  Local<Object> imageBitmapObj = info.This();

  Image *image = ObjectWrap::Unwrap<Image>(Local<Object>::Cast(info[0]));
  ImageBitmap *imageBitmap = new ImageBitmap(image);
  imageBitmap->Wrap(imageBitmapObj);

  Nan::SetAccessor(imageBitmapObj, JS_STR("width"), WidthGetter);
  Nan::SetAccessor(imageBitmapObj, JS_STR("height"), HeightGetter);
  Nan::SetAccessor(imageBitmapObj, JS_STR("data"), DataGetter);

  info.GetReturnValue().Set(imageBitmapObj);
}

NAN_GETTER(ImageBitmap::WidthGetter) {
  Nan::HandleScope scope;

  ImageBitmap *imageBitmap = ObjectWrap::Unwrap<ImageBitmap>(info.This());

  info.GetReturnValue().Set(JS_INT(imageBitmap->GetWidth()));
}

NAN_GETTER(ImageBitmap::HeightGetter) {
  Nan::HandleScope scope;

  ImageBitmap *imageBitmap = ObjectWrap::Unwrap<ImageBitmap>(info.This());

  info.GetReturnValue().Set(JS_INT(imageBitmap->GetHeight()));
}

NAN_GETTER(ImageBitmap::DataGetter) {
  Nan::HandleScope scope;

  ImageBitmap *imageBitmap = ObjectWrap::Unwrap<ImageBitmap>(info.This());

  if (imageBitmap->dataArray.IsEmpty()) {
    unsigned int width = imageBitmap->GetWidth();
    unsigned int height = imageBitmap->GetHeight();
    Local<ArrayBuffer> arrayBuffer = ArrayBuffer::New(Isolate::GetCurrent(), imageBitmap->GetData(), width * height * 4);

    Local<Uint8ClampedArray> uint8ClampedArray = Uint8ClampedArray::New(arrayBuffer, 0, arrayBuffer->ByteLength());
    imageBitmap->dataArray.Reset(uint8ClampedArray);
  }

  info.GetReturnValue().Set(Nan::New(imageBitmap->dataArray));
}

NAN_METHOD(ImageBitmap::CreateImageBitmap) {
  Nan::HandleScope scope;

  Local<Function> imageBitmapConstructor = Local<Function>::Cast(info.Callee()->Get(JS_STR("ImageBitmap")));
  if (info[0]->ToObject()->Get(JS_STR("constructor"))->ToObject()->Get(JS_STR("name"))->StrictEquals(JS_STR("HTMLImageElement"))) {
    Local<Value> arg = info[0]->ToObject()->Get(JS_STR("image"));
    Local<Value> argv[] = {
      arg,
    };
    Local<Object> imageBitmapObj = imageBitmapConstructor->NewInstance(sizeof(argv) / sizeof(argv[0]), argv);

    info.GetReturnValue().Set(imageBitmapObj);
  } else if (info[0]->ToObject()->Get(JS_STR("constructor"))->ToObject()->Get(JS_STR("name"))->StrictEquals(JS_STR("Blob"))) {
    Local<ArrayBufferView> buffer = Local<ArrayBufferView>::Cast(info[0]->ToObject()->Get(JS_STR("buffer")));
    Local<ArrayBuffer> arrayBufer = buffer->Buffer();

    Local<Function> imageConstructor = Local<Function>::Cast(info.Callee()->Get(JS_STR("Image")));
    Local<Value> argv1[] = {};
    Local<Object> imageObj = imageConstructor->NewInstance(sizeof(argv1) / sizeof(argv1[0]), argv1);
    Image *image = ObjectWrap::Unwrap<Image>(imageObj);
    image->Load((unsigned char *)arrayBufer->GetContents().Data() + buffer->ByteOffset(), buffer->ByteLength());

    Local<Value> argv2[] = {
      imageObj,
    };
    Local<Object> imageBitmapObj = imageBitmapConstructor->NewInstance(sizeof(argv2) / sizeof(argv2[0]), argv2);

    info.GetReturnValue().Set(imageBitmapObj);
  } else {
    Nan::ThrowError("Invalid arguments");
  }
}

ImageBitmap::ImageBitmap(Image *image) {
  imageData = new canvas::ImageData(image->image->getData());
}
ImageBitmap::~ImageBitmap () {
  delete imageData;
}
