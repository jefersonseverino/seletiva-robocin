/****************************************************************************
** Meta object code from reading C++ file 'main_window.h'
**
** Created by: The Qt Meta Object Compiler version 63 (Qt 4.8.7)
**
** WARNING! All changes made in this file will be lost!
*****************************************************************************/

#include "main_window.h"
#if !defined(Q_MOC_OUTPUT_REVISION)
#error "The header file 'main_window.h' doesn't include <QObject>."
#elif Q_MOC_OUTPUT_REVISION != 63
#error "This file was generated using the moc from 4.8.7. It"
#error "cannot be used with the include files from this version of Qt."
#error "(The moc has changed too much.)"
#endif

QT_BEGIN_MOC_NAMESPACE
static const uint qt_meta_data_MainWindow[] = {

 // content:
       6,       // revision
       0,       // classname
       0,    0, // classinfo
      41,   14, // methods
       0,    0, // properties
       0,    0, // enums/sets
       0,    0, // constructors
       0,       // flags
       1,       // signalCount

 // signals: signature, parameters, type, tag, flags
      12,   11,   11,   11, 0x05,

 // slots: signature, parameters, type, tag, flags
      26,   11,   11,   11, 0x08,
      36,   11,   11,   11, 0x08,
      47,   11,   11,   11, 0x08,
      68,   11,   11,   11, 0x08,
      79,   11,   11,   11, 0x08,
      92,   11,   11,   11, 0x08,
     103,   11,   11,   11, 0x08,
     119,  116,   11,   11, 0x08,
     143,  116,   11,   11, 0x08,
     167,  116,   11,   11, 0x08,
     189,  116,   11,   11, 0x08,
     217,   11,   11,   11, 0x08,
     227,   11,   11,   11, 0x08,
     240,   11,   11,   11, 0x08,
     254,   11,   11,   11, 0x08,
     301,  267,   11,   11, 0x08,
     328,   11,   11,   11, 0x08,
     339,   11,   11,   11, 0x08,
     347,   11,   11,   11, 0x08,
     366,   11,   11,   11, 0x08,
     382,   11,   11,   11, 0x08,
     400,  116,   11,   11, 0x08,
     421,  116,   11,   11, 0x08,
     440,  116,   11,   11, 0x08,
     467,  116,   11,   11, 0x08,
     493,  116,   11,   11, 0x08,
     515,  116,   11,   11, 0x08,
     546,   11,   11,   11, 0x08,
     558,  554,   11,   11, 0x08,
     584,   11,   11,   11, 0x08,
     612,  606,   11,   11, 0x08,
     636,  630,   11,   11, 0x08,
     665,  606,   11,   11, 0x08,
     693,  683,   11,   11, 0x08,
     739,  724,   11,   11, 0x08,
     800,  776,   11,   11, 0x08,
     854,  826,   11,   11, 0x08,
     885,   11,   11,   11, 0x08,
     903,   11,   11,   11, 0x08,
     955,  930,   11,   11, 0x08,

       0        // eod
};

static const char qt_meta_stringdata_MainWindow[] = {
    "MainWindow\0\0viewUpdated()\0newFile()\0"
    "openConf()\0openBackgroundConf()\0"
    "saveConf()\0saveConfAs()\0openData()\0"
    "saveDataAs()\0on\0setPlayerAutoMove(bool)\0"
    "setDataAutoSelect(bool)\0setSymmetryMode(bool)\0"
    "setConstraintEditMode(bool)\0addData()\0"
    "insertData()\0replaceData()\0deleteData()\0"
    "old_visual_index,new_visual_index\0"
    "changeSampleIndex(int,int)\0reverseY()\0"
    "train()\0toggleFullScreen()\0toggleToolBar()\0"
    "toggleStatusBar()\0setEnlargeMode(bool)\0"
    "setShowIndex(bool)\0setShowTriangulation(bool)\0"
    "setShowCircumcircle(bool)\0"
    "setAntialiasing(bool)\0"
    "toggleShowBackgroundData(bool)\0about()\0"
    "pos\0setPositionLabel(QPointF)\0"
    "editMenuAboutToShow()\0index\0"
    "selectSample(int)\0value\0"
    "selectSampleVisualIndex(int)\0"
    "deleteSample(int)\0index,x,y\0"
    "replaceBall(int,double,double)\0"
    "index,unum,x,y\0replacePlayer(int,int,double,double)\0"
    "origin_idx,terminal_idx\0"
    "deleteConstraint(int,int)\0"
    "idx,origin_idx,terminal_idx\0"
    "replaceConstraint(int,int,int)\0"
    "updateDataIndex()\0showConstraintEditDialog()\0"
    "first_index,second_index\0"
    "showConstraintEditDialog(int,int)\0"
};

void MainWindow::qt_static_metacall(QObject *_o, QMetaObject::Call _c, int _id, void **_a)
{
    if (_c == QMetaObject::InvokeMetaMethod) {
        Q_ASSERT(staticMetaObject.cast(_o));
        MainWindow *_t = static_cast<MainWindow *>(_o);
        switch (_id) {
        case 0: _t->viewUpdated(); break;
        case 1: _t->newFile(); break;
        case 2: _t->openConf(); break;
        case 3: _t->openBackgroundConf(); break;
        case 4: _t->saveConf(); break;
        case 5: _t->saveConfAs(); break;
        case 6: _t->openData(); break;
        case 7: _t->saveDataAs(); break;
        case 8: _t->setPlayerAutoMove((*reinterpret_cast< bool(*)>(_a[1]))); break;
        case 9: _t->setDataAutoSelect((*reinterpret_cast< bool(*)>(_a[1]))); break;
        case 10: _t->setSymmetryMode((*reinterpret_cast< bool(*)>(_a[1]))); break;
        case 11: _t->setConstraintEditMode((*reinterpret_cast< bool(*)>(_a[1]))); break;
        case 12: _t->addData(); break;
        case 13: _t->insertData(); break;
        case 14: _t->replaceData(); break;
        case 15: _t->deleteData(); break;
        case 16: _t->changeSampleIndex((*reinterpret_cast< int(*)>(_a[1])),(*reinterpret_cast< int(*)>(_a[2]))); break;
        case 17: _t->reverseY(); break;
        case 18: _t->train(); break;
        case 19: _t->toggleFullScreen(); break;
        case 20: _t->toggleToolBar(); break;
        case 21: _t->toggleStatusBar(); break;
        case 22: _t->setEnlargeMode((*reinterpret_cast< bool(*)>(_a[1]))); break;
        case 23: _t->setShowIndex((*reinterpret_cast< bool(*)>(_a[1]))); break;
        case 24: _t->setShowTriangulation((*reinterpret_cast< bool(*)>(_a[1]))); break;
        case 25: _t->setShowCircumcircle((*reinterpret_cast< bool(*)>(_a[1]))); break;
        case 26: _t->setAntialiasing((*reinterpret_cast< bool(*)>(_a[1]))); break;
        case 27: _t->toggleShowBackgroundData((*reinterpret_cast< bool(*)>(_a[1]))); break;
        case 28: _t->about(); break;
        case 29: _t->setPositionLabel((*reinterpret_cast< const QPointF(*)>(_a[1]))); break;
        case 30: _t->editMenuAboutToShow(); break;
        case 31: _t->selectSample((*reinterpret_cast< int(*)>(_a[1]))); break;
        case 32: _t->selectSampleVisualIndex((*reinterpret_cast< int(*)>(_a[1]))); break;
        case 33: _t->deleteSample((*reinterpret_cast< int(*)>(_a[1]))); break;
        case 34: _t->replaceBall((*reinterpret_cast< int(*)>(_a[1])),(*reinterpret_cast< double(*)>(_a[2])),(*reinterpret_cast< double(*)>(_a[3]))); break;
        case 35: _t->replacePlayer((*reinterpret_cast< int(*)>(_a[1])),(*reinterpret_cast< int(*)>(_a[2])),(*reinterpret_cast< double(*)>(_a[3])),(*reinterpret_cast< double(*)>(_a[4]))); break;
        case 36: _t->deleteConstraint((*reinterpret_cast< int(*)>(_a[1])),(*reinterpret_cast< int(*)>(_a[2]))); break;
        case 37: _t->replaceConstraint((*reinterpret_cast< int(*)>(_a[1])),(*reinterpret_cast< int(*)>(_a[2])),(*reinterpret_cast< int(*)>(_a[3]))); break;
        case 38: _t->updateDataIndex(); break;
        case 39: _t->showConstraintEditDialog(); break;
        case 40: _t->showConstraintEditDialog((*reinterpret_cast< int(*)>(_a[1])),(*reinterpret_cast< int(*)>(_a[2]))); break;
        default: ;
        }
    }
}

const QMetaObjectExtraData MainWindow::staticMetaObjectExtraData = {
    0,  qt_static_metacall 
};

const QMetaObject MainWindow::staticMetaObject = {
    { &QMainWindow::staticMetaObject, qt_meta_stringdata_MainWindow,
      qt_meta_data_MainWindow, &staticMetaObjectExtraData }
};

#ifdef Q_NO_DATA_RELOCATION
const QMetaObject &MainWindow::getStaticMetaObject() { return staticMetaObject; }
#endif //Q_NO_DATA_RELOCATION

const QMetaObject *MainWindow::metaObject() const
{
    return QObject::d_ptr->metaObject ? QObject::d_ptr->metaObject : &staticMetaObject;
}

void *MainWindow::qt_metacast(const char *_clname)
{
    if (!_clname) return 0;
    if (!strcmp(_clname, qt_meta_stringdata_MainWindow))
        return static_cast<void*>(const_cast< MainWindow*>(this));
    return QMainWindow::qt_metacast(_clname);
}

int MainWindow::qt_metacall(QMetaObject::Call _c, int _id, void **_a)
{
    _id = QMainWindow::qt_metacall(_c, _id, _a);
    if (_id < 0)
        return _id;
    if (_c == QMetaObject::InvokeMetaMethod) {
        if (_id < 41)
            qt_static_metacall(this, _c, _id, _a);
        _id -= 41;
    }
    return _id;
}

// SIGNAL 0
void MainWindow::viewUpdated()
{
    QMetaObject::activate(this, &staticMetaObject, 0, 0);
}
QT_END_MOC_NAMESPACE
