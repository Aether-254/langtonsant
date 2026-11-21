import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0430 : checkSingleBlackFast (18, 4) 6479 .west (-7, 0) (-19, -3) = true := by
  decide +kernel

end LangtonsAnt
