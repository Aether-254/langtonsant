import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0495 : checkSingleBlackFast (2, 15) 9815 .west (-13, -1) (-8, -23) = true := by
  decide +kernel

end LangtonsAnt
