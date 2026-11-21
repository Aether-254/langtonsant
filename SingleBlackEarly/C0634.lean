import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0634 : checkSingleBlackFast (10, -8) 30239 .west (-1, 10) (-35, 1) = true := by
  decide +kernel

end LangtonsAnt
