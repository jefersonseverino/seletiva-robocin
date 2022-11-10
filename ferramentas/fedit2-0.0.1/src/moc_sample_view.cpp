/****************************************************************************
** Meta object code from reading C++ file 'sample_view.h'
**
** Created by: The Qt Meta Object Compiler version 63 (Qt 4.8.7)
**
** WARNING! All changes made in this file will be lost!
*****************************************************************************/

#include "sample_view.h"
#if !defined(Q_MOC_OUTPUT_REVISION)
#error "The header file 'sample_view.h' doesn't include <QObject>."
#elif Q_MOC_OUTPUT_REVISION != 63
#error "This file was generated using the moc from 4.8.7. It"
#error "cannot be used with the include files from this version of Qt."
#error "(The moc has changed too much.)"
#endif

QT_BEGIN_MOC_NAMESPACE
static const uint qt_meta_data_SampleView[] = {

 // content:
       6,       // revision
       0,       // classname
       0,    0, // classinfo
       9,   14, // methods
       0,    0, // properties
       0,    0, // enums/sets
       0,    0, // constructors
       0,       // flags
       5,       // signalCount

 // signals: signature, parameters, type, tag, flags
      16,   12,   11,   11, 0x05,
      70,   36,   11,   11, 0x05,
     106,   12,   11,   11, 0x05,
     141,  133,   11,   11, 0x05,
     186,  173,   11,   11, 0x05,

 // slots: signature, parameters, type, tag, flags
     232,  224,   11,   11, 0x08,
     265,   11,   11,   11, 0x08,
     289,   11,   11,   11, 0x08,
     320,  308,   11,   11, 0x08,

       0        // eod
};

static const char qt_meta_stringdata_SampleView[] = {
    "SampleView\0\0idx\0sampleSelected(int)\0"
    "old_visual_index,new_visual_index\0"
    "sampleIndexChangeRequested(int,int)\0"
    "sampleDeleteRequested(int)\0idx,x,y\0"
    "ballReplaced(int,double,double)\0"
    "idx,unum,x,y\0playerReplaced(int,int,double,double)\0"
    "current\0setCurrentData(QTreeWidgetItem*)\0"
    "menuChangeSampleIndex()\0menuDeleteSample()\0"
    "index,value\0changeCoordinates(QModelIndex,double)\0"
};

void SampleView::qt_static_metacall(QObject *_o, QMetaObject::Call _c, int _id, void **_a)
{
    if (_c == QMetaObject::InvokeMetaMethod) {
        Q_ASSERT(staticMetaObject.cast(_o));
        SampleView *_t = static_cast<SampleView *>(_o);
        switch (_id) {
        case 0: _t->sampleSelected((*reinterpret_cast< int(*)>(_a[1]))); break;
        case 1: _t->sampleIndexChangeRequested((*reinterpret_cast< int(*)>(_a[1])),(*reinterpret_cast< int(*)>(_a[2]))); break;
        case 2: _t->sampleDeleteRequested((*reinterpret_cast< int(*)>(_a[1]))); break;
        case 3: _t->ballReplaced((*reinterpret_cast< int(*)>(_a[1])),(*reinterpret_cast< double(*)>(_a[2])),(*reinterpret_cast< double(*)>(_a[3]))); break;
        case 4: _t->playerReplaced((*reinterpret_cast< int(*)>(_a[1])),(*reinterpret_cast< int(*)>(_a[2])),(*reinterpret_cast< double(*)>(_a[3])),(*reinterpret_cast< double(*)>(_a[4]))); break;
        case 5: _t->setCurrentData((*reinterpret_cast< QTreeWidgetItem*(*)>(_a[1]))); break;
        case 6: _t->menuChangeSampleIndex(); break;
        case 7: _t->menuDeleteSample(); break;
        case 8: _t->changeCoordinates((*reinterpret_cast< const QModelIndex(*)>(_a[1])),(*reinterpret_cast< double(*)>(_a[2]))); break;
        default: ;
        }
    }
}

const QMetaObjectExtraData SampleView::staticMetaObjectExtraData = {
    0,  qt_static_metacall 
};

const QMetaObject SampleView::staticMetaObject = {
    { &QTreeWidget::staticMetaObject, qt_meta_stringdata_SampleView,
      qt_meta_data_SampleView, &staticMetaObjectExtraData }
};

#ifdef Q_NO_DATA_RELOCATION
const QMetaObject &SampleView::getStaticMetaObject() { return staticMetaObject; }
#endif //Q_NO_DATA_RELOCATION

const QMetaObject *SampleView::metaObject() const
{
    return QObject::d_ptr->metaObject ? QObject::d_ptr->metaObject : &staticMetaObject;
}

void *SampleView::qt_metacast(const char *_clname)
{
    if (!_clname) return 0;
    if (!strcmp(_clname, qt_meta_stringdata_SampleView))
        return static_cast<void*>(const_cast< SampleView*>(this));
    return QTreeWidget::qt_metacast(_clname);
}

int SampleView::qt_metacall(QMetaObject::Call _c, int _id, void **_a)
{
    _id = QTreeWidget::qt_metacall(_c, _id, _a);
    if (_id < 0)
        return _id;
    if (_c == QMetaObject::InvokeMetaMethod) {
        if (_id < 9)
            qt_static_metacall(this, _c, _id, _a);
        _id -= 9;
    }
    return _id;
}

// SIGNAL 0
void SampleView::sampleSelected(int _t1)
{
    void *_a[] = { 0, const_cast<void*>(reinterpret_cast<const void*>(&_t1)) };
    QMetaObject::activate(this, &staticMetaObject, 0, _a);
}

// SIGNAL 1
void SampleView::sampleIndexChangeRequested(int _t1, int _t2)
{
    void *_a[] = { 0, const_cast<void*>(reinterpret_cast<const void*>(&_t1)), const_cast<void*>(reinterpret_cast<const void*>(&_t2)) };
    QMetaObject::activate(this, &staticMetaObject, 1, _a);
}

// SIGNAL 2
void SampleView::sampleDeleteRequested(int _t1)
{
    void *_a[] = { 0, const_cast<void*>(reinterpret_cast<const void*>(&_t1)) };
    QMetaObject::activate(this, &staticMetaObject, 2, _a);
}

// SIGNAL 3
void SampleView::ballReplaced(int _t1, double _t2, double _t3)
{
    void *_a[] = { 0, const_cast<void*>(reinterpret_cast<const void*>(&_t1)), const_cast<void*>(reinterpret_cast<const void*>(&_t2)), const_cast<void*>(reinterpret_cast<const void*>(&_t3)) };
    QMetaObject::activate(this, &staticMetaObject, 3, _a);
}

// SIGNAL 4
void SampleView::playerReplaced(int _t1, int _t2, double _t3, double _t4)
{
    void *_a[] = { 0, const_cast<void*>(reinterpret_cast<const void*>(&_t1)), const_cast<void*>(reinterpret_cast<const void*>(&_t2)), const_cast<void*>(reinterpret_cast<const void*>(&_t3)), const_cast<void*>(reinterpret_cast<const void*>(&_t4)) };
    QMetaObject::activate(this, &staticMetaObject, 4, _a);
}
QT_END_MOC_NAMESPACE
