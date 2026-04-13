import * as React from 'react';
import { S } from '../styles';

export function InfoTip(props: { text: string }) {
    const [show, setShow] = React.useState(false);
    return (
        <span
            style={S.infoTipWrap}
            onMouseEnter={() => setShow(true)}
            onMouseLeave={() => setShow(false)}
        >
            <span style={S.infoTipIcon}>ⓘ</span>
            {show && (
                <span style={S.infoTipPopover}>{props.text}</span>
            )}
        </span>
    );
}
