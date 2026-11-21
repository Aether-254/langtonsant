import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0374 : checkSingleBlackFast (13, -4) 4634 .south (-12, -3) (-17, -6) = true := by
  decide +kernel

end LangtonsAnt
