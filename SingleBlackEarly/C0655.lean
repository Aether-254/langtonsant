import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0655 : checkSingleBlackFast (11, -10) 8375 .west (-7, 6) (-19, -13) = true := by
  decide +kernel

end LangtonsAnt
