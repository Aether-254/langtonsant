import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0815 : checkSingleBlackFast (24, -3) 12397 .west (-13, 5) (-23, -18) = true := by
  decide +kernel

end LangtonsAnt
