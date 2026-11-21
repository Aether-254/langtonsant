import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1898 : checkSingleBlackFast (-64, -43) 19821 .east (23, 13) (7, -46) = true := by
  decide +kernel

end LangtonsAnt
