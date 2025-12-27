export function jsonViewer(json: any, collapsible=false) {
    var TEMPLATES: { [tpl: string]: string } = {
        item: `<div class="json__item">
          <div class="json__key">%KEY%</div>
          <div class="json__value json__value--%TYPE%">%VALUE%</div>
        </div>`,
        // <input type="checkbox" class="json__toggle"/>
        itemCollapsible: `<details class="json__item json__item--collapsible">
          <summary>
            <div class="json__key">%KEY%</div>
            <div class="json__value json__value--type-%TYPE%">%VALUE%</div>
          </summary>
          %CHILDREN%
        </details>`,
        itemCollapsibleOpen: `<details class="json__item json__item--collapsible">
          <summary>
            <div class="json__key">%KEY%</div>
            <div class="json__value json__value--type-%TYPE%">%VALUE%</div>
          </summary>
          %CHILDREN%
        </details>`
    };

    function createItem(key: string, value: any, type: typeof value) {
        var element = TEMPLATES.item.replace('%KEY%', key);

        if(type == 'string') {
            element = element.replace('%VALUE%', '"' + value + '"');
        } else {
            element = element.replace('%VALUE%', value);
        }

        element = element.replace('%TYPE%', type);

        return element;
    }

    function createCollapsibleItem(key: string, value: any, type: typeof value, children: string) {
        var tpl: string = 
          collapsible
          ? 'itemCollapsibleOpen'
          : 'itemCollapsible';
          
        var element = TEMPLATES[tpl].replace('%KEY%', key);

        element = element.replace('%VALUE%', type);
        element = element.replace('%TYPE%', type);
        element = element.replace('%CHILDREN%', children);

        return element;
    }

    function handleChildren(key: string, value: any, type: typeof value) {
        var html = '';

        for(var item in value) { 
            var _key = item;
            var _val = value[item];

            html += handleItem(_key, _val);
        }

        return createCollapsibleItem(key, value, type, html);
    }

    function handleItem(key: string, value: any) {
        var type = typeof value;

        if(typeof value === 'object') {        
            return handleChildren(key, value, type);
        }

        return createItem(key, value, type);
    }

    function parseObject(obj: { [key: string]: any }) {
        var _result = '<div class="json">';

        for(var item in obj) { 
            var key = item;
            var value = obj[item];

            _result += handleItem(key, value);
        }

        _result += '</div>';

        return _result;
    }
    
    return parseObject(json);
};

