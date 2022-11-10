/****************************************************************************
** Meta object code from reading C++ file 'constraint_view.h'
**
** Created by: The Qt Meta Object Compiler version 63 (Qt 4.8.7)
**
** WARNING! All changes made in this file will be lost!
*****************************************************************************/

#include "constraint_view.h"
#if !defined(Q_MOC_OUTPUT_REVISION)
#error "The header file 'constraint_view.h' doesn't include <QObject>."
#elif Q_MOC_OUTPUT_REVISION != 63
#error "This file was generated using the moc from 4.8.7. It"
#error "cannot be used with the include files from this version of Qt."
#error "(The moc has changed too much.)"
#endif

QT_BEGIN_MOC_NAMESPACE
static const uint qt_meta_data_ConstraintView[] = {

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
      20,   16,   15,   15, 0x05,
      68,   44,   15,   15, 0x05,
     131,  103,   15,   15, 0x05,

 // slots: signature, parameters, type, tag, flags
     171,  163,   15,   15, 0x08,
     205,   15,   15,   15, 0x08,
     240,  228,   15,   15, 0x08,

       0        // eod
};

static const char qt_meta_stringdata_ConstraintView[] = {
    "ConstraintView\0\0idx\0constraintSelected(int)\0"
    "origin_idx,terminal_idx\0"
    "constraintDeleteRequested(int,int)\0"
    "idx,origin_idx,terminal_idx\0"
    "constraintReplaced(int,int,int)\0current\0"
    "setCurrentData(QTableWidgetItem*)\0"
    "menuDeleteConstraint()\0index,value\0"
    "changeConstraintIndex(QModelIndex,int)\0"
};

void ConstraintView::qt_static_metacall(QObject *_o, QMetaObject::Call _c, int _id, void **_a)
{
    if (_c == QMetaObject::InvokeMetaMethod) {
        Q_ASSERT(staticMetaObject.cast(_o));
        ConstraintView *_t = static_cast<ConstraintView *>(_o);
        switch (_id) {
        case 0: _t->constraintSelected((*reinterpret_cast< int(*)>(_a[1]))); break;
        case 1: _t->constraintDeleteRequested((*reinterpret_cast< int(*)>(_a[1])),(*reinterpret_cast< int(*)>(_a[2]))); break;
        case 2: _t->constraintReplaced((*reinterpret_cast< int(*)>(_a[1])),(*reinterpret_cast< int(*)>(_a[2])),(*reinterpret_cast< int(*)>(_a[3]))); break;
        case 3: _t->setCurrentData((*reinterpret_cast< QTableWidgetItem*(*)>(_a[1]))); break;
        case 4: _t->menuDeleteConstraint(); break;
        case 5: _t->changeConstraintIndex((*reinterpret_cast< const QModelIndex(*)>(_a[1])),(*reinterpret_cast< int(*)>(_a[2]))); break;
        default: ;
        }
    }
}

const QMetaObjectExtraData ConstraintView::staticMetaObjectExtraData = {
    0,  qt_static_metacall 
};

const QMetaObject ConstraintView::staticMetaObject = {
    { &QTableWidget::staticMetaObject, qt_meta_stringdata_ConstraintView,
      qt_meta_data_ConstraintView, &staticMetaObjectExtraData }
};

#ifdef Q_NO_DATA_RELOCATION
const QMetaObject &ConstraintView::getStaticMetaObject() { return staticMetaObject; }
#endif //Q_NO_DATA_RELOCATION

const QMetaObject *ConstraintView::metaObject() const
{
    return QObject::d_ptr->metaObject ? QObject::d_ptr->metaObject : &staticMetaObject;
}

void *ConstraintView::qt_metacast(const char *_clname)
{
    if (!_clname) return 0;
    if (!strcmp(_clname, qt_meta_stringdata_ConstraintView))
        return static_cast<void*>(const_cast< ConstraintView*>(this));
    return QTableWidget::qt_metacast(_clname);
}

int ConstraintView::qt_metacall(QMetaObject::Call _c, int _id, void **_a)
{
    _id = QTableWidget::qt_metacall(_c, _id, _a);
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
void ConstraintView::constraintSelected(int _t1)
{
    void *_a[] = { 0, const_cast<void*>(reinterpret_cast<const void*>(&_t1)) };
    QMetaObject::activate(this, &staticMetaObject, 0, _a);
}

// SIGNAL 1
void ConstraintView::constraintDeleteRequested(int _t1, int _t2)
{
    void *_a[] = { 0, const_cast<void*>(reinterpret_cast<const void*>(&_t1)), const_cast<void*>(reinterpret_cast<const void*>(&_t2)) };
    QMetaObject::activate(this, &staticMetaObject, 1, _a);
}

// SIGNAL 2
void ConstraintView::constraintReplaced(int _t1, int _t2, int _t3)
{
    void *_a[] = { 0, const_cast<void*>(reinterpret_cast<const void*>(&_t1)), const_cast<void*>(reinterpret_cast<const void*>(&_t2)), const_cast<void*>(reinterpret_cast<const void*>(&_t3)) };
    QMetaObject::activate(this, &staticMetaObject, 2, _a);
}
QT_END_MOC_NAMESPACE
