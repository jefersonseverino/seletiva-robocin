/****************************************************************************
** Meta object code from reading C++ file 'edit_canvas.h'
**
** Created by: The Qt Meta Object Compiler version 63 (Qt 4.8.7)
**
** WARNING! All changes made in this file will be lost!
*****************************************************************************/

#include "edit_canvas.h"
#if !defined(Q_MOC_OUTPUT_REVISION)
#error "The header file 'edit_canvas.h' doesn't include <QObject>."
#elif Q_MOC_OUTPUT_REVISION != 63
#error "This file was generated using the moc from 4.8.7. It"
#error "cannot be used with the include files from this version of Qt."
#error "(The moc has changed too much.)"
#endif

QT_BEGIN_MOC_NAMESPACE
static const uint qt_meta_data_EditCanvas[] = {

 // content:
       6,       // revision
       0,       // classname
       0,    0, // classinfo
       6,   14, // methods
       0,    0, // properties
       0,    0, // enums/sets
       0,    0, // constructors
       0,       // flags
       3,       // signalCount

 // signals: signature, parameters, type, tag, flags
      12,   11,   11,   11, 0x05,
      30,   26,   11,   11, 0x05,
      75,   50,   11,   11, 0x05,

 // slots: signature, parameters, type, tag, flags
     103,   11,   11,   11, 0x0a,
     112,   11,   11,   11, 0x0a,
     122,   11,   11,   11, 0x0a,

       0        // eod
};

static const char qt_meta_stringdata_EditCanvas[] = {
    "EditCanvas\0\0objectMoved()\0pos\0"
    "mouseMoved(QPointF)\0first_index,second_index\0"
    "constraintSelected(int,int)\0zoomIn()\0"
    "zoomOut()\0fitToScreen()\0"
};

void EditCanvas::qt_static_metacall(QObject *_o, QMetaObject::Call _c, int _id, void **_a)
{
    if (_c == QMetaObject::InvokeMetaMethod) {
        Q_ASSERT(staticMetaObject.cast(_o));
        EditCanvas *_t = static_cast<EditCanvas *>(_o);
        switch (_id) {
        case 0: _t->objectMoved(); break;
        case 1: _t->mouseMoved((*reinterpret_cast< const QPointF(*)>(_a[1]))); break;
        case 2: _t->constraintSelected((*reinterpret_cast< int(*)>(_a[1])),(*reinterpret_cast< int(*)>(_a[2]))); break;
        case 3: _t->zoomIn(); break;
        case 4: _t->zoomOut(); break;
        case 5: _t->fitToScreen(); break;
        default: ;
        }
    }
}

const QMetaObjectExtraData EditCanvas::staticMetaObjectExtraData = {
    0,  qt_static_metacall 
};

const QMetaObject EditCanvas::staticMetaObject = {
    { &QWidget::staticMetaObject, qt_meta_stringdata_EditCanvas,
      qt_meta_data_EditCanvas, &staticMetaObjectExtraData }
};

#ifdef Q_NO_DATA_RELOCATION
const QMetaObject &EditCanvas::getStaticMetaObject() { return staticMetaObject; }
#endif //Q_NO_DATA_RELOCATION

const QMetaObject *EditCanvas::metaObject() const
{
    return QObject::d_ptr->metaObject ? QObject::d_ptr->metaObject : &staticMetaObject;
}

void *EditCanvas::qt_metacast(const char *_clname)
{
    if (!_clname) return 0;
    if (!strcmp(_clname, qt_meta_stringdata_EditCanvas))
        return static_cast<void*>(const_cast< EditCanvas*>(this));
    return QWidget::qt_metacast(_clname);
}

int EditCanvas::qt_metacall(QMetaObject::Call _c, int _id, void **_a)
{
    _id = QWidget::qt_metacall(_c, _id, _a);
    if (_id < 0)
        return _id;
    if (_c == QMetaObject::InvokeMetaMethod) {
        if (_id < 6)
            qt_static_metacall(this, _c, _id, _a);
        _id -= 6;
    }
    return _id;
}

// SIGNAL 0
void EditCanvas::objectMoved()
{
    QMetaObject::activate(this, &staticMetaObject, 0, 0);
}

// SIGNAL 1
void EditCanvas::mouseMoved(const QPointF & _t1)
{
    void *_a[] = { 0, const_cast<void*>(reinterpret_cast<const void*>(&_t1)) };
    QMetaObject::activate(this, &staticMetaObject, 1, _a);
}

// SIGNAL 2
void EditCanvas::constraintSelected(int _t1, int _t2)
{
    void *_a[] = { 0, const_cast<void*>(reinterpret_cast<const void*>(&_t1)), const_cast<void*>(reinterpret_cast<const void*>(&_t2)) };
    QMetaObject::activate(this, &staticMetaObject, 2, _a);
}
QT_END_MOC_NAMESPACE
