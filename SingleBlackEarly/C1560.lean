import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1560 : checkSingleBlackFast (-33, -11) 25904 .south (0, -11) (-18, -19) = true := by
  decide +kernel

end LangtonsAnt
