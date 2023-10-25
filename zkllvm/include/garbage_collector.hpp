#pragma once
#include "data_structures.hpp"

class GarbageCollector {
public:
  class RefCountedObject {
  public:
    RefCountedObject(GarbageCollector &gc) noexcept : ref_count_(0), gc_(&gc) {}
    static RefCountedObject *
    newRefCountedObject(GarbageCollector &gc) noexcept {
      RefCountedObject *obj =
          static_cast<RefCountedObject *>(malloc(sizeof(RefCountedObject)));

      (obj->gc_) = &gc;
      obj->ref_count_ = 0;
      return obj;
    }
    void AddRef() noexcept { ref_count_++; }
    void Release() noexcept {
      ref_count_--;
      if (ref_count_ == 0) {
        gc_->deleteObject(this);
      }
    }

    // private:
    int ref_count_;
    GarbageCollector *gc_;
  };

  RefCountedObject *createObject() noexcept {
    RefCountedObject *obj = RefCountedObject::newRefCountedObject(*this);
    // new RefCountedObject(*this);
    objects_->push_back(obj);
    return obj;
  }
  void deleteObject(RefCountedObject *obj) noexcept {
    auto it = objects_->find(obj);
    if (it != objects_->end()) {
      (*it)->~RefCountedObject();
      free(*it);
      // delete *it;
      objects_->clear(it);
    }
  }
  void deleteAllReferences() noexcept {
    for (auto obj : *objects_) {
      obj->~RefCountedObject();
      free(obj);
      // delete obj;
    }
    objects_->clear();
  }

  GarbageCollector() noexcept {}
  ~GarbageCollector() noexcept {
    objects_->~LinkedList();
    free(objects_);
    free(this);
  }
  void init() noexcept { objects_ = LinkedList<RefCountedObject *>::create(); }

private:
  LinkedList<RefCountedObject *> *objects_;
};

GarbageCollector *newGarbageCollector() noexcept {
  GarbageCollector *gc =
      static_cast<GarbageCollector *>(malloc(sizeof(GarbageCollector)));
  gc->init();
  return gc;
}
