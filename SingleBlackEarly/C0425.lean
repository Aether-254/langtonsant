import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0425 : checkSingleBlackFast (19, 2) 26939 .west (-13, -6) (-21, -27) = true := by
  decide +kernel

end LangtonsAnt
