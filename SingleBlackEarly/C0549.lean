import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0549 : checkSingleBlackFast (9, -6) 23521 .west (-4, 2) (-30, -11) = true := by
  decide +kernel

end LangtonsAnt
